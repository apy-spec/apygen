use crate::analysis::abstract_state::{AbstractState, AbstractStateProxy};
use crate::analysis::fmt::fmt_set;
use crate::analysis::lattice::Join;
use crate::analysis::{DependencyGraphAnalyser, DummyAnalysisObserver, GraphAnalyser, analysis};
use crate::calls::{Arguments, BoundArguments};
use crate::constraint_graph::expressions::{
    BinaryOperator, Expression, ExpressionAnnotated, ExpressionAttribute, ExpressionBinary,
    ExpressionCall, ExpressionClass, ExpressionFunction, ExpressionImport, ExpressionOverride,
    ExpressionSubscript, ExpressionUnary, ExpressionVariableDefinition,
    ExpressionVariableReference, Namespace, SmolStr,
};
use crate::constraint_graph::graph::Graph;
use crate::constraint_graph::graph::dot::DiGraphDot;
use crate::constraint_graph::{
    Constraint, ConstraintGraph, ConstraintNode, Guard, ModuleDependentGraph,
};
use crate::expressions::literal_class::method_resolution_order;
use crate::expressions::{Call, Definition, PyEffects, PyTypeEval, gen_bool_value, type_literal};
use crate::identifiers::smol_str::format_smolstr;
use crate::identifiers::{Location, NamedQualifiedLocation, QualifiedLocation};
use crate::inference::{
    BUILTINS_MODULE, Base, ClassType, DEPTH_LIMIT, Deferred, DefinedVariables, Exception,
    ExceptionOrigin, FunctionType, ImportedModuleType, LiteralClass, LiteralFunction,
    LiteralImportedModule, LiteralMethod, NamespaceEvaluation, ProgramEvaluation, RaisedExceptions,
    Source, Sourced, StructuralDepth, StructuralWidth, Type, TypeInstance, TypeLiteral,
    WIDTH_LIMIT,
};
use imbl::ordmap::Entry;
use rayon::iter::{ParallelBridge, ParallelIterator};
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;
use std::fmt::{Debug, Display, Formatter};
use std::sync::Arc;
use thiserror::Error;

pub use apygen_analysis as analysis;
pub use apygen_constraint_graph as constraint_graph;
use apygen_constraint_graph::expressions::Parameter;
pub use apygen_identifiers as identifiers;
pub use apygen_inference as inference;
pub use apygen_primitives as primitives;
pub use imbl;
use imbl::shared_ptr::DefaultSharedPtr;

pub mod calls;
pub mod expressions;

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Join)]
pub struct EvaluationState {
    pub types: imbl::OrdMap<Arc<Expression>, Deferred<Sourced<Type>, Expression>>,
    pub return_value: Option<Deferred<Sourced<Type>, Expression>>,
    pub raised_exceptions: Deferred<RaisedExceptions, Expression>,
    pub defined_variables: DefinedVariables,
    pub type_variables: imbl::OrdMap<SmolStr, imbl::OrdSet<(Arc<Namespace>, Location)>>,
}

impl EvaluationState {
    pub fn get_variable_type(
        &self,
        variable_name: &SmolStr,
        locations: &imbl::OrdSet<(Arc<Namespace>, Location)>,
    ) -> Option<Deferred<Sourced<Type>, Expression>> {
        let mut ty = Deferred::known(Sourced::specified(Type::Never));
        for (namespace, location) in locations {
            let variable = Expression::VariableDefinition(ExpressionVariableDefinition::new(
                NamedQualifiedLocation::new(
                    variable_name.clone(),
                    location.clone(),
                    namespace.clone(),
                ),
            ));
            ty = ty.join(&self.types.get(&variable).cloned()?);
        }
        Some(ty)
    }

    pub fn get_type_attribute(
        &self,
        name: &SmolStr,
    ) -> Option<Deferred<Sourced<Type>, Expression>> {
        self.type_variables
            .get(name)
            .map(|locations| self.get_variable_type(name, locations).unwrap_or_default())
    }
}

impl Display for EvaluationState {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            for (expression, eval) in &self.types {
                writeln!(f, "{} = {}", expression, eval)?;
            }
            writeln!(f, "#variables = {}", self.defined_variables)?;
            writeln!(f, "#raise = {}", self.raised_exceptions)?;
            if let Some(return_value) = &self.return_value {
                writeln!(f, "#return = {}", return_value)?;
            }
            Ok(())
        } else {
            f.write_str("(evaluations: ")?;
            fmt_set(f, self.types.iter(), |f, (expression, eval)| {
                write!(f, "{}: {}", expression, eval)
            })?;
            if let Some(return_value) = &self.return_value {
                writeln!(f, ", return: {}", return_value)?;
            } else {
                f.write_str(", return: None")?;
            }
            write!(
                f,
                ", raised: {}, defined_variables: {})",
                self.raised_exceptions, self.defined_variables
            )
        }
    }
}

impl NamespaceEvaluation for EvaluationState {
    type Expression = Expression;

    fn attributes(
        &self,
    ) -> impl Iterator<Item = (&SmolStr, Deferred<Sourced<Type>, Self::Expression>)> {
        self.defined_variables
            .names
            .iter()
            .map(|(variable_name, locations)| {
                (
                    variable_name,
                    self.get_variable_type(variable_name, locations)
                        .unwrap_or_default(),
                )
            })
    }

    fn get_attribute(&self, name: &SmolStr) -> Option<Deferred<Sourced<Type>, Self::Expression>> {
        self.defined_variables
            .names
            .get(name)
            .map(|locations| self.get_variable_type(name, locations).unwrap_or_default())
    }

    fn raised_exceptions(&self) -> &Deferred<RaisedExceptions, Self::Expression> {
        &self.raised_exceptions
    }

    fn return_value(&self) -> &Option<Deferred<Sourced<Type>, Self::Expression>> {
        &self.return_value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Join)]
pub struct SolverState<N: Ord, S> {
    pub abstract_states: imbl::OrdMap<N, S>,
}

impl<N: Ord, S> SolverState<N, S> {
    pub fn new(abstract_states: imbl::OrdMap<N, S>) -> Self {
        Self { abstract_states }
    }
}

impl<N: Ord, S> Default for SolverState<N, S> {
    fn default() -> Self {
        Self {
            abstract_states: imbl::OrdMap::default(),
        }
    }
}

impl<N: Clone + Ord + Send + Sync, S: Clone + Send + Sync> AbstractState for SolverState<N, S> {
    type Key = N;
    type AbstractValue = S;

    fn get(&self, key: &Self::Key) -> Option<&Self::AbstractValue> {
        self.abstract_states.get(key)
    }

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::AbstractValue> {
        self.abstract_states.get_mut(key)
    }

    fn get_or_insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue {
        self.abstract_states.entry(key).or_insert(abstract_value)
    }

    fn insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue {
        match self.abstract_states.entry(key) {
            Entry::Occupied(entry) => {
                let previous_abstract_value = entry.into_mut();
                *previous_abstract_value = abstract_value;
                previous_abstract_value
            }
            Entry::Vacant(entry) => entry.insert(abstract_value),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum EvaluatorMode {
    Normal,
    Annotation,
}

#[derive(Debug, Clone, Error)]
pub enum EvaluationError {
    #[error("the expression uses a deferred expression")]
    Deferred,
    #[error("the expression is an invalid annotation")]
    InvalidAnnotation,
    #[error("failed to get the reference to the qualified name {module}.{id}")]
    QualifiedNameReferenceError { module: SmolStr, id: SmolStr },
    #[error("failed to get the reference to the namespace {0}")]
    NamespaceReferenceError(Namespace),
}

pub struct ExpressionEvaluator<'a> {
    pub mode: EvaluatorMode,
    pub namespace: &'a Namespace,
    pub namespace_dependency_graph: &'a NamespaceDependencyGraph,
}

impl<'a> ExpressionEvaluator<'a> {
    pub fn new(
        mode: EvaluatorMode,
        namespace: &'a Namespace,
        namespace_dependency_graph: &'a NamespaceDependencyGraph,
    ) -> Self {
        Self {
            mode,
            namespace,
            namespace_dependency_graph,
        }
    }

    pub fn with_namespace(&self, namespace: &'a Namespace) -> Self {
        Self::new(self.mode, namespace, self.namespace_dependency_graph)
    }

    pub fn with_mode(&self, mode: EvaluatorMode) -> Self {
        Self::new(mode, self.namespace, self.namespace_dependency_graph)
    }

    pub fn extract_deferred<T: Clone>(
        deferred: Deferred<T, Expression>,
    ) -> Result<T, EvaluationError> {
        match deferred.to_value() {
            Some(sourced) => Ok(sourced),
            None => Err(EvaluationError::Deferred),
        }
    }

    pub fn find_type(
        abstract_state: &impl AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        module: &SmolStr,
        name: &SmolStr,
    ) -> Result<Type, EvaluationError> {
        match TypeInstance::from_qualified_name(abstract_state, module, name) {
            Some(type_instance) => Ok(Type::Instance(type_instance)),
            None => Err(EvaluationError::QualifiedNameReferenceError {
                module: module.clone(),
                id: name.clone(),
            }),
        }
    }

    pub fn evaluate_expression_variable_definition<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_variable_definition: &ExpressionVariableDefinition,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let namespace = expression_variable_definition.namespace();

        let Some(evaluation_state) = abstract_state.get(namespace) else {
            return Err(EvaluationError::NamespaceReferenceError(
                namespace.as_ref().clone(),
            ));
        };

        Ok(PyTypeEval::with_default_effects(Self::extract_deferred(
            evaluation_state
                .types
                .get(&Expression::VariableDefinition(
                    expression_variable_definition.clone(),
                ))
                .cloned()
                .unwrap_or_default(),
        )?))
    }

    pub fn evaluate_expression_variable_reference<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_variable_reference: &ExpressionVariableReference,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        if let Some(evaluation_state) = abstract_state.get(self.namespace) {
            if let Some(deferred_ty) = if matches!(self.mode, EvaluatorMode::Normal) {
                evaluation_state.get_attribute(&expression_variable_reference.name)
            } else {
                evaluation_state.get_type_attribute(&expression_variable_reference.name)
            } {
                return Ok(PyTypeEval::with_default_effects(Self::extract_deferred(
                    deferred_ty,
                )?));
            }
        };

        if let Some(parent_namespace) = self.namespace.parent() {
            return self
                .with_namespace(parent_namespace.as_ref())
                .evaluate_expression_variable_reference(
                    abstract_state,
                    expression_variable_reference,
                );
        }

        if *self.namespace.module_name() != BUILTINS_MODULE {
            return self
                .with_namespace(&Namespace::Module(BUILTINS_MODULE))
                .evaluate_expression_variable_reference(
                    abstract_state,
                    expression_variable_reference,
                );
        }

        if matches!(self.mode, EvaluatorMode::Normal) {
            Ok(PyTypeEval::raise(Exception::new(
                Sourced::inferred(Self::find_type(
                    abstract_state,
                    &BUILTINS_MODULE,
                    &SmolStr::new_static("NameError"),
                )?),
                ExceptionOrigin::Specified, // TODO: fix origin
            )))
        } else {
            Err(EvaluationError::InvalidAnnotation)
        }
    }

    pub fn evaluate_expression_annotated<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_annotated: &ExpressionAnnotated,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let annotation_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.with_mode(EvaluatorMode::Annotation)
                .evaluate_expression(abstract_state, &expression_annotated.annotation)?
        );

        let Type::Literal(type_literal) = annotation_sourced_ty.data else {
            return Err(EvaluationError::InvalidAnnotation);
        };

        let base = match type_literal.as_ref() {
            TypeLiteral::Class(literal_class) => Base::Class(literal_class.clone()),
            TypeLiteral::TypeAlias(literal_type_alias) => {
                Base::TypeAlias(literal_type_alias.clone())
            }
            TypeLiteral::Generic(literal_generic) => Base::Generic(literal_generic.clone()),
            _ => return Err(EvaluationError::InvalidAnnotation),
        };

        Ok(PyTypeEval::new(
            Sourced::specified(Type::Instance(TypeInstance {
                base,
                arguments: imbl::Vector::new(),
            })),
            effects,
        ))
    }

    pub fn evaluate_expression_override<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_override: &ExpressionOverride,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        self.evaluate_expression(abstract_state, &expression_override.previous)
    }

    pub fn evaluate_expression_function<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_function: &ExpressionFunction,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let mut parameters = imbl::Vector::new();
        for (parameter, expression) in &expression_function.parameters {
            parameters.push_back((
                parameter.clone(),
                if let Some(expression) = expression {
                    Some(
                        if let Ok(eval) = self.evaluate_expression(abstract_state, expression) {
                            Deferred::known(pytype_consume_or_return_ok!(effects, eval))
                        } else {
                            Deferred::unknown(imbl::OrdSet::unit(expression.clone()))
                        },
                    )
                } else {
                    None
                },
            ))
        }

        let mut raised_exceptions = Deferred::known(RaisedExceptions::default());
        for expression in &expression_function.exceptions {
            if let Ok(eval) = self.evaluate_expression(abstract_state, expression) {
                raised_exceptions.value.exceptions.insert(Exception::new(
                    pytype_consume_or_return_ok!(effects, eval),
                    ExceptionOrigin::Specified,
                ));
            } else {
                raised_exceptions.expressions.insert(expression.clone());
            }
        }

        let return_value = if let Some(return_value) = &expression_function.return_value {
            Some(
                if let Ok(eval) = self.evaluate_expression(abstract_state, return_value) {
                    Deferred::known(pytype_consume_or_return_ok!(effects, eval))
                } else {
                    Deferred::unknown(imbl::OrdSet::unit(return_value.clone()))
                },
            )
        } else {
            None
        };

        Ok(PyTypeEval::new(
            Sourced::inferred(Type::new_literal(TypeLiteral::Function(LiteralFunction {
                value: Arc::new(FunctionType {
                    program_entity: expression_function.program_entity.clone(),
                    generics: Default::default(),
                    is_async: expression_function.is_async,
                }),
            }))),
            effects.with_definitions(imbl::OrdSet::unit((
                Namespace::NamedProgramEntity(expression_function.program_entity.clone()),
                Definition::new(parameters, raised_exceptions, return_value),
            ))),
        ))
    }

    pub fn evaluate_expression_class<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_class: &ExpressionClass,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let class_namespace =
            Namespace::NamedProgramEntity(expression_class.program_entity.clone());

        Ok(PyTypeEval::new(
            Sourced::inferred(Type::new_literal(TypeLiteral::Class(LiteralClass {
                value: Arc::new(ClassType {
                    program_entity: expression_class.program_entity.clone(),
                    generics: Default::default(),
                    bases: Default::default(),
                    keyword_arguments: Default::default(),
                    is_abstract: false,
                }),
            }))),
            PyEffects::new(),
        ))
    }

    pub fn evaluate_expression_import<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_import: &ExpressionImport,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let namespace = Namespace::Module(expression_import.module.clone());

        if abstract_state.contains(&namespace) {
            Ok(PyTypeEval::with_default_effects(Sourced::inferred(
                Type::new_literal(TypeLiteral::ImportedModule(LiteralImportedModule {
                    value: Arc::new(ImportedModuleType {
                        module: expression_import.module.clone(),
                    }),
                })),
            )))
        } else {
            Ok(PyTypeEval::unknown())
        }
    }

    /// References: https://docs.python.org/3/howto/descriptor.html
    fn evaluate_attributes<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        value_ty: &Type,
        name: &SmolStr,
        instance_arguments: Option<&imbl::Vector<Arc<Type>>>,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        match value_ty {
            Type::Instance(type_instance) => self.evaluate_attributes(
                abstract_state,
                &type_instance.base.as_type(),
                name,
                Some(&type_instance.arguments),
            ),
            Type::Union(type_union) => {
                let mut eval = PyTypeEval::never();
                for ty in type_union.types() {
                    eval = eval.join(&self.evaluate_attributes(abstract_state, ty, name, None)?);
                }
                Ok(eval)
            }
            Type::Intersection(type_intersection) => {
                let mut eval = PyTypeEval::never();
                for ty in type_intersection {
                    eval = eval.join(&self.evaluate_attributes(abstract_state, ty, name, None)?);
                }
                Ok(eval)
            }
            Type::Literal(type_literal) => match type_literal.as_ref() {
                TypeLiteral::Class(literal_class) => {
                    // TODO: add support for descriptors
                    let Some(mro) = method_resolution_order(literal_class) else {
                        return Ok(PyTypeEval::raise(Exception::new(
                            Sourced::inferred(Type::Any),
                            ExceptionOrigin::Specified, // TODO: fix origin
                        )));
                    };

                    for class in mro {
                        let class_namespace =
                            Namespace::NamedProgramEntity(class.value.program_entity.clone());

                        let Some(evaluation_state) = abstract_state.get(&class_namespace) else {
                            return Err(EvaluationError::Deferred);
                        };

                        let Some(deferred_ty) = evaluation_state.get_attribute(name) else {
                            continue;
                        };

                        let mut sourced_ty = Self::extract_deferred(deferred_ty)?;

                        if let Type::Literal(type_literal) = &sourced_ty.data {
                            if let TypeLiteral::Function(literal_function) = type_literal.as_ref() {
                                if let Some(arguments) = instance_arguments {
                                    sourced_ty = Sourced::inferred(Type::new_literal(
                                        TypeLiteral::Method(LiteralMethod {
                                            class: class.value.clone(),
                                            function: literal_function.value.clone(),
                                            arguments: arguments.clone(),
                                        }),
                                    ));
                                }
                            }
                        };

                        return Ok(PyTypeEval::with_default_effects(sourced_ty));
                    }

                    Ok(PyTypeEval::unknown())
                }
                _ => {
                    let Some(type_instance) = type_literal.as_type_instance(abstract_state) else {
                        let (module, class_name) = type_literal.type_name();
                        return Err(EvaluationError::QualifiedNameReferenceError {
                            module,
                            id: SmolStr::new_static(class_name),
                        });
                    };
                    self.evaluate_attributes(
                        abstract_state,
                        &Type::Instance(type_instance),
                        name,
                        None,
                    )
                }
            },
            _ => Ok(PyTypeEval::unknown()), // TODO: add missing cases
        }
    }

    pub fn evaluate_expression_attribute<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_attribute: &ExpressionAttribute,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let value_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_attribute.value)?
        );

        self.evaluate_attributes(
            abstract_state,
            &value_sourced_ty.data,
            &expression_attribute.attribute,
            None,
        )
    }

    pub fn evaluate_expression_subscript<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_subscript: &ExpressionSubscript,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let value_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_subscript.value)?
        );
        let get_item_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_attributes(
                abstract_state,
                &value_sourced_ty.data,
                &SmolStr::new_static("__getitem__"),
                None,
            )?
        );
        let slice_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_subscript.slice)?
        );

        let sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_call(
                abstract_state,
                &get_item_sourced_ty.data,
                Arguments::new().add_positional_argument(slice_sourced_ty.data)
            )?
        );

        Ok(PyTypeEval::new(sourced_ty, effects))
    }

    pub fn evaluate_call<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        ty: &Type,
        arguments: Arguments,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let Type::Literal(literal) = ty else {
            return Ok(PyTypeEval::unknown()); // TODO: add support for unions, etc
        };

        match literal.as_ref() {
            TypeLiteral::Function(literal_function) => {
                let function_namespace =
                    Namespace::NamedProgramEntity(literal_function.value.program_entity.clone());

                let Some(evaluation_state) = abstract_state.get(&function_namespace) else {
                    return Ok(PyTypeEval::unknown());
                };

                let bound_arguments = arguments
                    .bind(
                        self.namespace_dependency_graph
                            .nodes()
                            .get(&function_namespace)
                            .unwrap()
                            .definition
                            .parameters
                            .iter()
                            .map(|(parameter, _)| parameter.clone())
                            .collect::<Vec<_>>(),
                    )
                    .unwrap_or_default();

                Ok(PyTypeEval::new(
                    Sourced::inferred(if let Some(return_value) = &evaluation_state.return_value {
                        Self::extract_deferred(return_value.clone())?.data.clone()
                    } else {
                        Type::Any
                    }),
                    PyEffects::new()
                        .with_exceptions(Self::extract_deferred(
                            evaluation_state.raised_exceptions.clone(),
                        )?)
                        .with_calls(imbl::OrdSet::unit(Call::new(
                            Arc::new(function_namespace),
                            abstract_state.clone(),
                            bound_arguments,
                        ))),
                ))
            }
            TypeLiteral::Method(literal_method) => self.evaluate_call(
                abstract_state,
                &Type::Literal(Arc::new(TypeLiteral::Function(LiteralFunction {
                    value: literal_method.function.clone(),
                }))),
                arguments.with_self(Type::Literal(Arc::new(TypeLiteral::Class(LiteralClass {
                    value: literal_method.class.clone(),
                })))),
            ),
            TypeLiteral::Class(literal_class) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::Instance(TypeInstance {
                    base: Base::Class(literal_class.clone()),
                    arguments: imbl::Vector::new(),
                })),
            )),
            _ => Ok(PyTypeEval::unknown()), // TODO: add support for classes, etc
        }
    }

    pub fn evaluate_expression_call<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_call: &ExpressionCall,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_call.target)?
        );

        let mut arguments = Arguments::new();

        for argument in &expression_call.positional_arguments {
            let argument_sourced_ty = pytype_consume_or_return_ok!(
                effects,
                self.evaluate_expression(abstract_state, &argument)?
            );

            arguments.positional.push(argument_sourced_ty.data);
        }
        for keyword_argument in &expression_call.keyword_arguments {
            if let Some(name) = &keyword_argument.name {
                let keyword_argument_sourced_ty = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_expression(abstract_state, &keyword_argument.value)?
                );

                arguments
                    .keyword
                    .insert(name.clone(), keyword_argument_sourced_ty.data);
            }
        }

        self.evaluate_call(abstract_state, &sourced_ty.data, arguments)
    }

    pub fn evaluate_expression_unary<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_unary: &ExpressionUnary,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let operand_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_unary.operand)?
        );

        let sourced_ty = match operand_sourced_ty.data {
            Type::Literal(type_literal) => {
                pytype_consume_or_return_ok!(
                    effects,
                    type_literal::call_unary_op(type_literal.as_ref(), expression_unary.operator)
                )
            }
            Type::Never | Type::NoReturn => unreachable!("operand_ty should not be unreachable"),
            _ => return Ok(PyTypeEval::unknown()), // TODO: add other cases
        };

        Ok(PyTypeEval::new(sourced_ty, effects))
    }

    pub fn evaluate_binary_operation<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        left_ty: &Type,
        operator: BinaryOperator,
        right_ty: &Type,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        match (left_ty, right_ty) {
            (Type::Literal(left), Type::Literal(right)) => Ok(type_literal::call_binary_op(
                left.as_ref(),
                operator,
                right.as_ref(),
            )),
            (Type::Instance(_), _) => {
                let mut effects = PyEffects::new();

                let Some(method_name) = operator.method_name() else {
                    return Ok(PyTypeEval::unknown()); // TODO: fix
                };

                let method_sourced_ty = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_attributes(
                        abstract_state,
                        left_ty,
                        &format_smolstr!("__{}__", method_name),
                        None
                    )?
                );

                let return_type = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_call(
                        abstract_state,
                        &method_sourced_ty.data,
                        Arguments::new().add_positional_argument(right_ty.clone()),
                    )?
                );

                Ok(PyTypeEval::new(return_type, effects))
            }
            (_, Type::Instance(_)) => {
                let mut effects = PyEffects::new();

                let Some(method_name) = operator.method_name() else {
                    return Ok(PyTypeEval::unknown()); // TODO: fix
                };

                let method_sourced_ty = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_attributes(
                        abstract_state,
                        right_ty,
                        &format_smolstr!("__r{}__", method_name),
                        None
                    )?
                );

                let return_type = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_call(
                        abstract_state,
                        &method_sourced_ty.data,
                        Arguments::new().add_positional_argument(left_ty.clone()),
                    )?
                );

                Ok(PyTypeEval::new(return_type, effects))
            }
            (Type::Union(left_type_union), Type::Union(right_type_union)) => {
                let mut type_eval = PyTypeEval::never();
                for ty in left_type_union.types() {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        abstract_state,
                        ty,
                        operator,
                        right_ty,
                    )?);
                }
                for ty in right_type_union.types() {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        abstract_state,
                        left_ty,
                        operator,
                        ty,
                    )?);
                }
                Ok(type_eval)
            }
            (Type::Union(left_type_union), _) => {
                let mut type_eval = PyTypeEval::never();
                for ty in left_type_union.types() {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        abstract_state,
                        ty,
                        operator,
                        right_ty,
                    )?);
                }
                Ok(type_eval)
            }
            (_, Type::Union(right_type_union)) => {
                let mut type_eval = PyTypeEval::never();
                for ty in right_type_union.types() {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        abstract_state,
                        left_ty,
                        operator,
                        ty,
                    )?);
                }
                Ok(type_eval)
            }
            (Type::Any, _) | (_, Type::Any) => Ok(PyTypeEval::unknown()),
            (Type::Never, _) | (_, Type::Never) | (Type::NoReturn, _) | (_, Type::NoReturn) => {
                unreachable!()
            }
            _ => Ok(PyTypeEval::unknown()), // TODO: add support for the rest
        }
    }

    pub fn evaluate_expression_binary<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression_binary: &ExpressionBinary,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut effects = PyEffects::new();

        let left_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_binary.left)?
        );
        let right_sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_binary.right)?
        );

        let sourced_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_binary_operation(
                abstract_state,
                &left_sourced_ty.data,
                expression_binary.operator,
                &right_sourced_ty.data
            )?
        );

        Ok(PyTypeEval::new(sourced_ty, effects))
    }

    pub fn evaluate_expression<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expression: &Expression,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let Some(evaluation_state) = abstract_state.get(self.namespace) else {
            return Err(EvaluationError::NamespaceReferenceError(
                self.namespace.clone(),
            ));
        };

        if let Some(deferred_ty) = evaluation_state.types.get(expression) {
            return Ok(PyTypeEval::with_default_effects(Self::extract_deferred(
                deferred_ty.clone(),
            )?));
        }

        match expression {
            Expression::VariableDefinition(expression_variable) => {
                self.evaluate_expression_variable_definition(abstract_state, expression_variable)
            }
            Expression::VariableReference(expression_forward_variable) => self
                .evaluate_expression_variable_reference(
                    abstract_state,
                    expression_forward_variable,
                ),
            Expression::Annotated(expression_annotated) => {
                self.evaluate_expression_annotated(abstract_state, expression_annotated)
            }
            Expression::Override(expression_override) => {
                self.evaluate_expression_override(abstract_state, expression_override)
            }
            Expression::Function(expression_function) => {
                self.evaluate_expression_function(abstract_state, expression_function)
            }
            Expression::Class(expression_class) => {
                self.evaluate_expression_class(abstract_state, expression_class)
            }
            Expression::Import(expression_import) => {
                self.evaluate_expression_import(abstract_state, expression_import)
            }
            Expression::Attribute(expression_attribute) => {
                self.evaluate_expression_attribute(abstract_state, expression_attribute)
            }
            Expression::Subscript(expression_subscript) => {
                self.evaluate_expression_subscript(abstract_state, expression_subscript)
            }
            Expression::Call(expression_call) => {
                self.evaluate_expression_call(abstract_state, expression_call)
            }
            Expression::Unary(expression_unary) => {
                self.evaluate_expression_unary(abstract_state, expression_unary)
            }
            Expression::Binary(expression_binary) => {
                self.evaluate_expression_binary(abstract_state, expression_binary)
            }
            Expression::LiteralInteger(literal_integer) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_integer_literal(literal_integer.clone())),
            )),
            Expression::LiteralFloat(literal_float) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_float_literal(literal_float.clone())),
            )),
            Expression::LiteralComplex(literal_complex) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_complex_literal(literal_complex.clone())),
            )),
            Expression::LiteralString(literal_string) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_string_literal(literal_string.clone())),
            )),
            Expression::LiteralBytes(literal_bytes) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_bytes_literal(literal_bytes.clone())),
            )),
            Expression::LiteralBoolean(literal_boolean) => Ok(PyTypeEval::with_default_effects(
                Sourced::inferred(Type::new_boolean_literal(literal_boolean.clone())),
            )),
            Expression::LiteralNone => Ok(PyTypeEval::with_default_effects(Sourced::inferred(
                Type::new_literal(TypeLiteral::None),
            ))),
            Expression::LiteralEllipsis => Ok(PyTypeEval::with_default_effects(Sourced::inferred(
                Type::new_literal(TypeLiteral::Ellipsis),
            ))),
        }
    }

    pub fn evaluate_expressions<
        'e,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        abstract_state: &S,
        expressions: impl IntoIterator<Item = &'e Expression>,
    ) -> Result<PyTypeEval<S>, EvaluationError> {
        let mut eval = PyTypeEval::with_default_effects(Sourced::specified(Type::Never));

        for expression in expressions {
            eval = eval.join(&self.evaluate_expression(abstract_state, expression)?);
        }

        Ok(eval)
    }
}

pub struct ConstraintSolver<'s> {
    pub namespace: &'s Namespace,
    pub definition: &'s Definition,
    pub constraint_graph: &'s ConstraintGraph,
    pub program_evaluation: &'s dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
    pub namespace_dependency_graph: &'s NamespaceDependencyGraph,
}

impl<'s> ConstraintSolver<'s> {
    pub fn new(
        namespace: &'s Namespace,
        definition: &'s Definition,
        constraint_graph: &'s ConstraintGraph,
        program_evaluation: &'s dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        namespace_dependency_graph: &'s NamespaceDependencyGraph,
    ) -> Self {
        Self {
            namespace,
            definition,
            constraint_graph,
            program_evaluation,
            namespace_dependency_graph,
        }
    }

    pub fn evaluator(&self, mode: EvaluatorMode) -> ExpressionEvaluator<'_> {
        ExpressionEvaluator::new(mode, self.namespace, self.namespace_dependency_graph)
    }

    pub fn evaluate_expression<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        mode: EvaluatorMode,
        program_evaluation: &S,
        expression: &Expression,
    ) -> Deferred<PyTypeEval<S>, Expression> {
        match self
            .evaluator(mode)
            .evaluate_expression(program_evaluation, expression)
        {
            Ok(eval) => Deferred::known(eval),
            Err(_) => Deferred::unknown(imbl::OrdSet::unit(Arc::new(expression.clone()))),
        }
    }

    pub fn evaluate_expressions<
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState> + Clone + Ord,
    >(
        &self,
        mode: EvaluatorMode,
        program_evaluation: &S,
        expressions: &imbl::OrdSet<Expression>,
    ) -> Deferred<PyTypeEval<S>, Expression> {
        match self
            .evaluator(mode)
            .evaluate_expressions(program_evaluation, expressions)
        {
            Ok(eval) => Deferred::known(eval),
            Err(_) => Deferred::unknown(
                expressions
                    .iter()
                    .map(|expression| Arc::new(expression.clone()))
                    .collect(),
            ),
        }
    }
}

impl<'s> GraphAnalyser for ConstraintSolver<'s> {
    type Node = ConstraintNode;
    type AbstractState = (
        AbstractStateProxy<'s, Namespace, EvaluationState, ProgramEvaluation<EvaluationState>>,
        imbl::OrdSet<(
            QualifiedLocation,
            Call<
                AbstractStateProxy<
                    's,
                    Namespace,
                    EvaluationState,
                    ProgramEvaluation<EvaluationState>,
                >,
            >,
        )>,
        imbl::OrdSet<(Namespace, Definition)>,
    );
    type AnalysisState = SolverState<Self::Node, Self::AbstractState>;
    type Error = Infallible;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error> {
        Ok(std::iter::once(ConstraintNode::Entry))
    }

    fn next_nodes(
        &self,
        node: &Self::Node,
    ) -> Result<impl Iterator<Item = &Self::Node>, Self::Error> {
        Ok(self
            .constraint_graph
            .edges
            .get(node)
            .into_iter()
            .flat_map(|tos| tos.keys()))
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        Ok(SolverState::default())
    }

    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::AbstractState, Self::Error> {
        let (mut program_evaluation, mut calls, mut definitions) =
            analysis_state.get_clone(node).unwrap_or_else(|| {
                (
                    AbstractStateProxy::new(
                        self.program_evaluation,
                        ProgramEvaluation::new(imbl::OrdMap::unit(
                            self.namespace.clone(),
                            EvaluationState::default(),
                        )),
                    ),
                    imbl::OrdSet::default(),
                    imbl::OrdSet::default(),
                )
            });

        match &node {
            ConstraintNode::Entry => {
                let evaluation_state =
                    program_evaluation.get_or_insert_default(self.namespace.clone());

                let (arguments, _) = self.namespace_dependency_graph.inputs(self.namespace);

                for (parameter, deferred_ty) in arguments {
                    evaluation_state.defined_variables.names.insert(
                        parameter.name.named_qualified_location.name.clone(),
                        imbl::OrdSet::unit((
                            parameter.name.named_qualified_location.namespace.clone(),
                            parameter.name.named_qualified_location.location.clone(),
                        )),
                    );
                    evaluation_state.type_variables.insert(
                        parameter.name.named_qualified_location.name.clone(),
                        imbl::OrdSet::unit((
                            parameter.name.named_qualified_location.namespace.clone(),
                            parameter.name.named_qualified_location.location.clone(),
                        )),
                    );
                    evaluation_state.types.insert(
                        Arc::new(Expression::VariableDefinition(parameter.name.clone())),
                        if let Some(deferred_ty) = &deferred_ty {
                            deferred_ty.clone()
                        } else {
                            Deferred::known(Sourced::inferred(Type::Any))
                        },
                    );
                }

                evaluation_state.raised_exceptions = self.definition.exceptions.clone();
                evaluation_state.return_value = self.definition.return_value.clone();
            }
            ConstraintNode::Constraint { location, .. } => {
                if let Some(constraints) = self.constraint_graph.nodes.get(node) {
                    for constraint in constraints {
                        match constraint {
                            Constraint::Type(type_constraint) => {
                                let deferred = self.evaluate_expression(
                                    EvaluatorMode::Normal,
                                    &program_evaluation,
                                    &type_constraint.left,
                                );
                                let deferred_ty = deferred.clone().map(|eval| eval.value);
                                let deferred_raised_exceptions =
                                    deferred.clone().map(|eval| eval.effects.exceptions);

                                let evaluation_state = program_evaluation
                                    .get_or_insert_default(self.namespace.clone());

                                evaluation_state
                                    .types
                                    .entry(type_constraint.right.clone())
                                    .and_modify(|previous_deferred| {
                                        *previous_deferred = previous_deferred.join(&deferred_ty)
                                    })
                                    .or_insert(deferred_ty);
                                evaluation_state.raised_exceptions = evaluation_state
                                    .raised_exceptions
                                    .join(&deferred_raised_exceptions);
                                if let Some(location) = location {
                                    for call in deferred.value.effects.calls {
                                        calls.insert((
                                            QualifiedLocation::new(
                                                location.clone(),
                                                Arc::new(self.namespace.clone()),
                                            ),
                                            call.clone(),
                                        ));
                                    }
                                }
                                definitions.extend(deferred.value.effects.definitions);
                            }
                            Constraint::Return(return_constraint) => {
                                let deferred = self.evaluate_expression(
                                    EvaluatorMode::Normal,
                                    &program_evaluation,
                                    &return_constraint.expression,
                                );
                                let deferred_ty = deferred.clone().map(|eval| eval.value);
                                let deferred_raised_exceptions =
                                    deferred.map(|eval| eval.effects.exceptions);

                                let evaluation_state = program_evaluation
                                    .get_or_insert_default(self.namespace.clone());

                                if let Some(return_value) = &evaluation_state.return_value {
                                    if !matches!(
                                        // TODO: fix
                                        return_value.value.source,
                                        Source::Specified
                                    ) {
                                        evaluation_state.return_value =
                                            Some(Deferred::known(deferred_ty.value));
                                    }
                                } else {
                                    evaluation_state.return_value =
                                        Some(Deferred::known(deferred_ty.value));
                                }
                                evaluation_state.raised_exceptions = evaluation_state
                                    .raised_exceptions
                                    .join(&deferred_raised_exceptions);
                            }
                            Constraint::DefinedVariable(expression) => {
                                let evaluation_state = program_evaluation
                                    .get_or_insert_default(self.namespace.clone());

                                evaluation_state.defined_variables.names.insert(
                                    expression.named_qualified_location.name.clone(),
                                    imbl::OrdSet::unit((
                                        expression.named_qualified_location.namespace.clone(),
                                        expression.named_qualified_location.location.clone(),
                                    )),
                                );
                                evaluation_state.type_variables.insert(
                                    expression.named_qualified_location.name.clone(),
                                    imbl::OrdSet::unit((
                                        expression.named_qualified_location.namespace.clone(),
                                        expression.named_qualified_location.location.clone(),
                                    )),
                                );
                            }
                        }
                    }
                }
            }
            _ => {}
        }

        Ok((program_evaluation, calls, definitions))
    }

    fn update_abstract_state(
        &self,
        _analysis_state: &Self::AnalysisState,
        from: &Self::Node,
        to: &Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error> {
        let (mut new_abstract_state, calls, definitions) = abstract_state.clone();

        let guards = self
            .constraint_graph
            .edges
            .get(from)
            .unwrap()
            .get(to)
            .unwrap();

        let mut should_ignore = !guards.is_empty();

        for guard in guards {
            match guard {
                Guard::ForwardReference => {
                    let evaluation_state =
                        new_abstract_state.get_or_insert_default(self.namespace.clone());

                    if evaluation_state
                        .types
                        .values()
                        .all(|ty| ty.expressions.is_empty())
                        && evaluation_state.raised_exceptions.expressions.is_empty()
                        && evaluation_state
                            .return_value
                            .as_ref()
                            .map(|deferred_ty| deferred_ty.expressions.is_empty())
                            .unwrap_or(true)
                        && definitions.iter().all(|(_, definition)| {
                            definition.parameters.iter().all(|(_, deferred_ty_option)| {
                                deferred_ty_option
                                    .as_ref()
                                    .map(|deferred_ty| deferred_ty.expressions.is_empty())
                                    .unwrap_or(true)
                            }) && definition.exceptions.expressions.is_empty()
                                && definition
                                    .return_value
                                    .as_ref()
                                    .map(|deferred_ty| deferred_ty.expressions.is_empty())
                                    .unwrap_or(true)
                        })
                    {
                        continue;
                    }

                    evaluation_state.type_variables = evaluation_state
                        .type_variables
                        .clone()
                        .union(evaluation_state.defined_variables.names.clone());
                    evaluation_state.defined_variables.names.clear();
                    should_ignore = false;
                }
                Guard::IsTrue(expression) => {
                    let deferred = self.evaluate_expression(
                        EvaluatorMode::Normal,
                        &new_abstract_state,
                        &expression,
                    );

                    if let Some(eval) = deferred.to_value() {
                        if let Some(bool_value) = gen_bool_value(&eval.value.data) {
                            if !bool_value {
                                continue;
                            }
                        }
                    }

                    should_ignore = false;
                }
                Guard::IsFalse(expression) => {
                    let deferred = self.evaluate_expression(
                        EvaluatorMode::Normal,
                        &new_abstract_state,
                        &expression,
                    );

                    if let Some(eval) = deferred.to_value() {
                        if let Some(bool_value) = gen_bool_value(&eval.value.data) {
                            if bool_value {
                                continue;
                            }
                        }
                    }

                    should_ignore = false;
                }
                Guard::Succeed(expression) => {
                    let deferred = self.evaluate_expression(
                        EvaluatorMode::Normal,
                        &new_abstract_state,
                        &expression,
                    );

                    if let Some(eval) = deferred.to_value() {
                        if is_sourced_type_unreachable!(eval.value) {
                            continue;
                        }
                    }

                    should_ignore = false;
                }
                Guard::Raise { expression, .. } => {
                    let deferred = self.evaluate_expression(
                        EvaluatorMode::Normal,
                        &new_abstract_state,
                        &expression,
                    );

                    if let Some(eval) = deferred.as_value() {
                        if eval.effects.exceptions.exceptions.is_empty() {
                            continue;
                        }
                    }

                    let evaluation_state =
                        new_abstract_state.get_or_insert_default(self.namespace.clone());

                    evaluation_state.raised_exceptions = evaluation_state
                        .raised_exceptions
                        .join(&deferred.map(|eval| eval.effects.exceptions));

                    should_ignore = false;
                }
            }
        }

        if should_ignore {
            Ok(None)
        } else {
            Ok(Some((new_abstract_state, calls, definitions)))
        }
    }

    fn get_abstract_state<'a>(
        &self,
        analysis_state: &'a Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Option<&'a Self::AbstractState>, Self::Error> {
        Ok(analysis_state.abstract_states.get(node))
    }

    fn set_abstract_state(
        &self,
        analysis_state: &mut Self::AnalysisState,
        node: &Self::Node,
        abstract_state: Self::AbstractState,
    ) -> Result<(), Self::Error> {
        analysis_state
            .abstract_states
            .insert(node.clone(), abstract_state);
        Ok(())
    }

    fn merge(
        &self,
        _analysis_state: &Self::AnalysisState,
        _node: &Self::Node,
        (left_abstract_state, left_calls, left_definitions): &Self::AbstractState,
        (right_abstract_state, right_calls, right_definitions): &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error> {
        assert!(std::ptr::addr_eq(
            left_abstract_state.abstract_state,
            self.program_evaluation
        ));
        assert!(std::ptr::addr_eq(
            right_abstract_state.abstract_state,
            self.program_evaluation
        ));

        let mut new_abstract_state = AbstractStateProxy::new(
            self.program_evaluation,
            left_abstract_state.proxy.join(&right_abstract_state.proxy),
        );

        if let Some(evaluation_state) = new_abstract_state.get(&self.namespace) {
            let new_evaluations = evaluation_state
                .types
                .clone()
                .into_iter()
                .map(|(expression, mut deferred)| {
                    while deferred.value.data.width() > WIDTH_LIMIT {
                        deferred.value = match deferred.value.data {
                            Type::Union(type_union) => {
                                let mut new_ty = Type::Never;
                                for ty in type_union.into_types() {
                                    new_ty =
                                        new_ty.join(&if let Type::Literal(type_literal) = &ty {
                                            type_literal
                                                .as_type_instance(&new_abstract_state)
                                                .map(|type_instance| Type::Instance(type_instance))
                                                .unwrap_or(Type::Any)
                                        } else {
                                            ty
                                        });
                                }
                                Sourced::inferred(new_ty)
                            }
                            _ => Sourced::inferred(Type::Any),
                        };
                    }

                    if deferred.value.data.depth() > DEPTH_LIMIT {
                        deferred.value = Sourced::inferred(Type::Any);
                    }

                    (expression, deferred)
                })
                .collect();

            new_abstract_state
                .get_mut(&self.namespace)
                .expect("evaluation_state should exists")
                .types = new_evaluations;
        }

        Ok((
            new_abstract_state,
            left_calls.join(&right_calls),
            left_definitions.join(&right_definitions),
        ))
    }

    fn optimise(
        &self,
        analysis_state: &mut Self::AnalysisState,
        worklist: &mut BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        let mut marked = BTreeSet::new();

        for worklist_node in worklist.iter() {
            if marked.contains(worklist_node) {
                continue;
            }

            let mut to_remove = BTreeSet::from_iter([worklist_node]);
            while let Some(node) = to_remove.pop_first() {
                for next_node in self.next_nodes(node)? {
                    if next_node != worklist_node
                        && *next_node != ConstraintNode::Entry
                        && analysis_state.abstract_states.contains_key(next_node)
                        && self
                            .constraint_graph
                            .predecessor_iter(next_node)
                            .all(|predecessor| predecessor == node || marked.contains(predecessor))
                    {
                        marked.insert(next_node);
                        to_remove.insert(next_node);
                    }
                }
            }
        }

        *worklist = worklist
            .extract_if(.., |node| !marked.contains(node))
            .collect();

        for node in marked {
            analysis_state.abstract_states.remove(node);
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EdgeCall {
    pub location: Location,
    pub context: ProgramEvaluation<EvaluationState>,
    pub arguments: BoundArguments,
}

impl EdgeCall {
    pub fn new(
        location: Location,
        context: ProgramEvaluation<EvaluationState>,
        arguments: BoundArguments,
    ) -> Self {
        Self {
            location,
            context,
            arguments,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum EdgeKind {
    Definition,
    Call(EdgeCall),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct NamespaceData {
    pub definition: Definition,
    pub dependents: imbl::OrdSet<Namespace>,
    pub dependencies: imbl::OrdSet<Namespace>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamespaceDependencyGraph {
    nodes: imbl::HashMap<Namespace, NamespaceData>,
    edges: imbl::HashMap<(Namespace, Namespace), imbl::OrdSet<EdgeKind>>,
}

impl NamespaceDependencyGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_calls(
        &self,
        calls: impl IntoIterator<Item = ((Namespace, Namespace), EdgeCall)>,
    ) -> Self {
        let mut new_graph = self.clone();
        for ((dependency, namespace), call) in calls {
            new_graph.add_dependency(dependency, namespace.clone(), EdgeKind::Call(call));
        }
        new_graph
    }

    pub fn with_sub_definitions(
        &self,
        sub_definitions: impl IntoIterator<Item = (Namespace, Definition)>,
    ) -> Self {
        let mut new_graph = self.clone();
        for (namespace, definition) in sub_definitions {
            new_graph.add_dependency(
                namespace
                    .parent()
                    .expect("should always exist")
                    .as_ref()
                    .clone(),
                namespace.clone(),
                EdgeKind::Definition,
            );
            new_graph
                .nodes
                .entry(namespace.clone())
                .or_default()
                .definition = definition.clone();
        }
        new_graph
    }

    pub fn calls(
        &self,
        namespace: &Namespace,
    ) -> impl Iterator<Item = ((Namespace, Namespace), EdgeCall)> {
        self.nodes
            .get(namespace)
            .into_iter()
            .flat_map(move |namespace_data| {
                namespace_data
                    .dependencies
                    .iter()
                    .flat_map(move |dependency| {
                        self.edges
                            .get(&(dependency.clone(), namespace.clone()))
                            .into_iter()
                            .flat_map(move |edge_kinds| {
                                edge_kinds
                                    .iter()
                                    .filter_map(move |edge_kind| match edge_kind {
                                        EdgeKind::Definition => None,
                                        EdgeKind::Call(call) => Some((
                                            (dependency.clone(), namespace.clone()),
                                            call.clone(),
                                        )),
                                    })
                            })
                    })
            })
    }

    pub fn callers(&self, namespace: &Namespace) -> impl Iterator<Item = (Namespace, EdgeCall)> {
        self.nodes
            .get(namespace)
            .into_iter()
            .flat_map(move |namespace_data| {
                namespace_data.dependents.iter().flat_map(move |dependent| {
                    self.edges
                        .get(&(namespace.clone(), dependent.clone()))
                        .into_iter()
                        .flat_map(move |edge_kinds| {
                            edge_kinds
                                .iter()
                                .filter_map(move |edge_kind| match edge_kind {
                                    EdgeKind::Definition => None,
                                    EdgeKind::Call(call) => Some((dependent.clone(), call.clone())),
                                })
                        })
                })
            })
    }

    pub fn inputs(
        &self,
        namespace: &Namespace,
    ) -> (
        imbl::OrdMap<Parameter, Option<Deferred<Sourced<Type>, Expression>>>,
        imbl::OrdMap<QualifiedLocation, ProgramEvaluation<EvaluationState>>,
    ) {
        let mut call_sites = imbl::OrdMap::default();
        let mut arguments = imbl::OrdMap::default();
        if let Some(namespace_data) = self.nodes.get(namespace) {
            arguments.extend(namespace_data.definition.parameters.iter().cloned());
        }
        for (namespace, edge_call) in self.callers(namespace) {
            call_sites.insert(
                QualifiedLocation::new(edge_call.location.clone(), Arc::new(namespace.clone())),
                edge_call.context,
            );
            for (parameter, ty) in edge_call.arguments.variables {
                match arguments.entry(parameter.clone()) {
                    Entry::Occupied(entry) => {
                        let current_deferred_ty: &mut Option<Deferred<Sourced<Type>, Expression>> =
                            entry.into_mut();

                        *current_deferred_ty =
                            if let Some(current_deferred_ty) = current_deferred_ty {
                                if current_deferred_ty.value.source > ty.source {
                                    Some(current_deferred_ty.clone())
                                } else {
                                    Some(current_deferred_ty.join(&Deferred::known(ty)))
                                }
                            } else {
                                Some(Deferred::known(ty))
                            };
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(Some(Deferred::known(ty)));
                    }
                }
            }
        }

        (arguments, call_sites)
    }

    pub fn sub_definitions(
        &self,
        namespace: &Namespace,
    ) -> impl Iterator<Item = (Namespace, Definition)> {
        self.nodes
            .get(namespace)
            .into_iter()
            .flat_map(|namespace_data| {
                namespace_data.dependents.iter().filter_map(|dependent| {
                    self.edges
                        .get(&(namespace.clone(), dependent.clone()))
                        .and_then(|edge_kinds| {
                            if edge_kinds
                                .iter()
                                .any(|edge_kind| matches!(edge_kind, EdgeKind::Definition))
                            {
                                self.nodes.get(dependent).map(|dependent_namespace_data| {
                                    (
                                        dependent.clone(),
                                        dependent_namespace_data.definition.clone(),
                                    )
                                })
                            } else {
                                None
                            }
                        })
                })
            })
    }
}

impl Default for NamespaceDependencyGraph {
    fn default() -> Self {
        Self {
            nodes: imbl::HashMap::default(),
            edges: imbl::HashMap::default(),
        }
    }
}

impl NamespaceDependencyGraph {
    pub fn nodes(&self) -> &imbl::HashMap<Namespace, NamespaceData> {
        &self.nodes
    }
    pub fn edges(&self) -> &imbl::HashMap<(Namespace, Namespace), imbl::OrdSet<EdgeKind>> {
        &self.edges
    }
    pub fn add_dependency(&mut self, dependency: Namespace, node: Namespace, edge_kind: EdgeKind) {
        self.nodes
            .entry(dependency.clone())
            .or_default()
            .dependents
            .insert(node.clone());
        self.nodes
            .entry(node.clone())
            .or_default()
            .dependencies
            .insert(dependency.clone());
        self.edges
            .entry((dependency, node))
            .or_default()
            .insert(edge_kind);
    }
    pub fn remove_dependency(&mut self, dependency: &Namespace, node: &Namespace) {
        self.edges.remove(&(dependency.clone(), node.clone()));
        if let Some(entry) = self.nodes.get_mut(dependency) {
            entry.dependents.remove(node);
        }
        if let Some(entry) = self.nodes.get_mut(node) {
            entry.dependencies.remove(dependency);
        }
    }
}

impl Display for NamespaceDependencyGraph {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{ nodes: {:?}, edges: {:?} }}", self.nodes, self.edges)
    }
}

impl Graph for NamespaceDependencyGraph {
    type Node = Namespace;
    type NodeData = NamespaceData;
    type EdgeData = imbl::OrdSet<EdgeKind>;

    fn node_data_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)> {
        self.nodes.iter()
    }

    fn edge_data_iter(
        &self,
    ) -> impl Iterator<Item = ((&Self::Node, &Self::Node), &Self::EdgeData)> {
        self.edges
            .iter()
            .map(|((from, to), edge_data)| ((from, to), edge_data))
    }
}

impl DiGraphDot for NamespaceDependencyGraph {
    fn fmt_node(
        &self,
        f: &mut Formatter<'_>,
        node: &Self::Node,
        _node_data: &Self::NodeData,
    ) -> std::fmt::Result {
        write!(f, "    \"{}\" [label=\"{}\"]\n", node, node)
    }

    fn fmt_edge(
        &self,
        f: &mut Formatter<'_>,
        (from, to): (&Self::Node, &Self::Node),
        edge_data: &Self::EdgeData,
    ) -> std::fmt::Result {
        write!(
            f,
            "    \"{}\" -> \"{}\" [label=\"{:?}\"]\n",
            from, to, edge_data
        )
    }
}

pub fn solve_namespace(
    namespace: &Namespace,
    definition: &Definition,
    constraint_graph: &ConstraintGraph,
    abstract_state: &dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
    namespace_dependency_graph: &NamespaceDependencyGraph,
) -> Result<
    (
        ProgramEvaluation<EvaluationState>,
        BTreeMap<(Namespace, Namespace), EdgeCall>,
        BTreeMap<Namespace, Definition>,
    ),
    Infallible,
> {
    let mut abstract_state_proxy = AbstractStateProxy::with_default_proxy(abstract_state);
    let mut namespace_dependency_graph = namespace_dependency_graph.clone();

    let mut calls = BTreeMap::default();
    let mut definitions = BTreeMap::default();

    let mut previous_evaluation_state: Option<EvaluationState> = None;
    let mut previous_calls: BTreeMap<_, _> = namespace_dependency_graph.calls(namespace).collect();
    loop {
        abstract_state_proxy.insert(namespace.clone(), EvaluationState::default());

        let mut solver_state = analysis(
            &ConstraintSolver::new(
                &namespace,
                definition,
                constraint_graph,
                &abstract_state_proxy,
                &namespace_dependency_graph,
            ),
            &mut DummyAnalysisObserver::default(),
        )?;

        let evaluation_state =
            if let Some((program_evaluation, _, _)) = solver_state.get(&ConstraintNode::TypeExit) {
                let mut evaluation_state = program_evaluation.get_clone_or_default(namespace);

                if let Some(exception_evaluation_state) = solver_state
                    .get(&ConstraintNode::ExceptionExit)
                    .and_then(|(program_evaluation, _, _)| program_evaluation.get(namespace))
                {
                    evaluation_state.types = evaluation_state
                        .types
                        .join(&exception_evaluation_state.types);
                    evaluation_state.raised_exceptions = evaluation_state
                        .raised_exceptions
                        .join(&exception_evaluation_state.raised_exceptions);
                }

                evaluation_state
            } else {
                solver_state
                    .get(&ConstraintNode::ExceptionExit)
                    .and_then(|(program_evaluation, _, _)| program_evaluation.get(namespace))
                    .cloned()
                    .unwrap_or_default()
            };

        let (new_calls, new_definitions) = solver_state
            .abstract_states
            .remove(&ConstraintNode::Exit)
            .map(|(program_evaluation, calls, definitions)| {
                assert_eq!(program_evaluation.proxy.states.len(), 1);
                (
                    calls
                        .into_iter()
                        .map(|(qualified_location, call)| {
                            (
                                (call.target.as_ref().clone(), namespace.clone()),
                                EdgeCall::new(
                                    qualified_location.location,
                                    call.context.proxy,
                                    call.arguments,
                                ),
                            )
                        })
                        .collect(),
                    definitions.into_iter().collect(),
                )
            })
            .unwrap_or_else(|| (BTreeMap::default(), BTreeMap::default()));

        drop(solver_state);

        let new_evaluation_state = abstract_state_proxy
            .insert(namespace.clone(), evaluation_state)
            .clone();

        if Some(&new_evaluation_state) == previous_evaluation_state.as_ref()
            && new_calls == previous_calls
        {
            calls.extend(new_calls);
            definitions.extend(new_definitions);
            return Ok((abstract_state_proxy.proxy, calls, definitions));
        }

        namespace_dependency_graph = namespace_dependency_graph
            .with_calls(new_calls.clone())
            .with_sub_definitions(new_definitions.clone());

        let (sub_program_evaluation, sub_calls, sub_definitions) = constraint_graph
            .subgraphs
            .iter()
            .par_bridge()
            .map(|(sub_namespace, subgraph)| {
                solve_namespace(
                    sub_namespace,
                    &new_definitions
                        .get(sub_namespace)
                        .unwrap_or(&Definition::default()),
                    subgraph,
                    &abstract_state_proxy,
                    &namespace_dependency_graph,
                )
            })
            .try_reduce(
                || {
                    (
                        ProgramEvaluation::default(),
                        BTreeMap::default(),
                        BTreeMap::default(),
                    )
                },
                |(mut program_evaluation_acc, mut calls_acc, mut definitions_acc),
                 (new_program_evaluation, new_calls, new_definitions)| {
                    program_evaluation_acc
                        .states
                        .extend(new_program_evaluation.states);
                    calls_acc.extend(new_calls);
                    definitions_acc.extend(new_definitions);
                    Ok((program_evaluation_acc, calls_acc, definitions_acc))
                },
            )?;

        abstract_state_proxy.proxy.states = sub_program_evaluation.states;
        namespace_dependency_graph = namespace_dependency_graph
            .with_calls(sub_calls.clone())
            .with_sub_definitions(sub_definitions.clone());

        calls = sub_calls;
        definitions = sub_definitions;

        previous_evaluation_state = Some(new_evaluation_state);
        previous_calls = new_calls;
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ModuleConstraintSolverAnalysisState {
    pub program_evaluation: ProgramEvaluation<EvaluationState>,
    pub namespace_dependency_graph: NamespaceDependencyGraph,
}

pub struct ModuleConstraintSolver<'a> {
    pub graph: &'a ModuleDependentGraph,
}

impl<'a> ModuleConstraintSolver<'a> {
    pub fn new(graph: &'a ModuleDependentGraph) -> Self {
        Self { graph }
    }

    fn get_namespaces<'n>(&'n self, namespace: &'n Namespace) -> Option<BTreeSet<&'n Namespace>> {
        self.graph
            .get_constraint_graph(namespace)
            .map(|constraint_graph| {
                constraint_graph
                    .subgraphs
                    .keys()
                    .filter_map(|sub_namespace| self.get_namespaces(sub_namespace))
                    .flatten()
                    .chain(std::iter::once(namespace))
                    .collect()
            })
    }
}

impl DependencyGraphAnalyser for ModuleConstraintSolver<'_> {
    type Node = SmolStr;
    type InputState = BTreeMap<
        Namespace,
        (
            imbl::OrdMap<Parameter, Option<Deferred<Sourced<Type>, Expression>>>,
            imbl::OrdSet<Option<QualifiedLocation>>,
        ),
    >;
    type OutputState = BTreeMap<Namespace, EvaluationState>;
    type AbstractState = (
        ProgramEvaluation<EvaluationState>,
        BTreeMap<(Namespace, Namespace), EdgeCall>,
        BTreeMap<Namespace, Definition>,
    );
    type AnalysisState = ModuleConstraintSolverAnalysisState;
    type Error = Infallible;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error> {
        Ok(std::iter::once(BUILTINS_MODULE))
    }
    fn dependency_nodes<'a>(
        &'a self,
        analysis_state: &'a Self::AnalysisState,
        node: &'a Self::Node,
    ) -> Result<impl Iterator<Item = &'a Self::Node>, Self::Error> {
        Ok(self
            .get_namespaces(&Namespace::Module(node.clone()))
            .unwrap()
            .into_iter()
            .filter_map(|namespace| {
                Some(
                    &analysis_state
                        .namespace_dependency_graph
                        .nodes()
                        .get(namespace)?
                        .dependencies,
                )
            })
            .flatten()
            .filter_map(|dependency_namespace| {
                let dependency_module_name = dependency_namespace.module_name();
                if node != dependency_module_name {
                    Some(dependency_module_name)
                } else {
                    None
                }
            })
            .collect::<BTreeSet<_>>()
            .into_iter())
    }
    fn dependent_nodes<'a>(
        &'a self,
        analysis_state: &'a Self::AnalysisState,
        node: &'a Self::Node,
    ) -> Result<impl Iterator<Item = &'a Self::Node>, Self::Error> {
        Ok(self
            .get_namespaces(&Namespace::Module(node.clone()))
            .unwrap()
            .into_iter()
            .filter_map(|namespace| {
                Some(
                    &analysis_state
                        .namespace_dependency_graph
                        .nodes()
                        .get(namespace)?
                        .dependents,
                )
            })
            .flatten()
            .filter_map(|dependent_namespace| {
                let dependent_module_name = dependent_namespace.module_name();
                if node != dependent_module_name {
                    Some(dependent_module_name)
                } else {
                    None
                }
            })
            .collect::<BTreeSet<_>>()
            .into_iter())
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        let mut analysis_state = ModuleConstraintSolverAnalysisState::default();
        for (module_name, dependent_module_names) in &self.graph.dependents {
            for dependent_module_name in dependent_module_names {
                analysis_state.namespace_dependency_graph.add_dependency(
                    Namespace::Module(module_name.clone()),
                    Namespace::Module(dependent_module_name.clone()),
                    EdgeKind::Definition,
                );
            }
        }
        Ok(analysis_state)
    }
    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::AbstractState, Self::Error> {
        let namespace = Namespace::Module(node.clone());
        let constraint_graph = self.graph.get_constraint_graph(&namespace).unwrap();

        solve_namespace(
            &namespace,
            &Definition::default(),
            constraint_graph,
            &analysis_state.program_evaluation,
            &analysis_state.namespace_dependency_graph,
        )
    }
    fn merge(
        &self,
        analysis_state: &Self::AnalysisState,
        (new_program_evaluation, new_calls, new_definitions): Self::AbstractState,
    ) -> Result<Self::AnalysisState, Self::Error> {
        let mut new_analysis_state = analysis_state.clone();

        new_analysis_state.namespace_dependency_graph = new_analysis_state
            .namespace_dependency_graph
            .with_calls(new_calls)
            .with_sub_definitions(new_definitions);
        new_analysis_state
            .program_evaluation
            .states
            .extend(new_program_evaluation.states);

        Ok(new_analysis_state)
    }
    fn get_input_state(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::InputState, Self::Error> {
        Ok(self
            .get_namespaces(&Namespace::Module(node.clone()))
            .unwrap_or_default()
            .into_iter()
            .map(|namespace| {
                let (arguments, call_sites) =
                    analysis_state.namespace_dependency_graph.inputs(&namespace);

                (
                    namespace.clone(),
                    (arguments, call_sites.keys().cloned().collect()),
                )
            })
            .collect())
    }
    fn get_output_state(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::OutputState, Self::Error> {
        Ok(self
            .get_namespaces(&Namespace::Module(node.clone()))
            .unwrap_or_default()
            .into_iter()
            .map(|namespace| {
                (
                    namespace.clone(),
                    analysis_state
                        .program_evaluation
                        .get_clone_or_default(namespace),
                )
            })
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inference::BUILTINS_MODULE;
    use apygen_analysis::dependencies_analysis;
    use apygen_analysis::log::LogAnalysisObserver;
    use apygen_constraint_builder::{ModuleLoader, analyse_program};
    use indoc::indoc;
    use rstest::rstest;
    use std::collections::HashMap;

    fn init_logger() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    pub struct TestModuleLoader {
        pub modules: HashMap<SmolStr, String>,
    }

    impl ModuleLoader for TestModuleLoader {
        type Error = Infallible;
        fn load(&self, module_name: &SmolStr) -> Result<String, Self::Error> {
            Ok(self.modules.get(module_name).cloned().unwrap())
        }
    }

    const TEST_BUILTINS: &str = indoc! {r##"
        class int:
            def __add__(self, value: int, /) -> int: ...

        class NameError:
            pass
    "##};

    #[rstest]
    fn test_builtins_constraints_solving() {
        init_logger();

        let expected_expressions = indoc! {r##"
        builtins:
            NameError@{builtins[4:6]} = Inferred(class(builtins[NameError@{4:6}]))
            int@{builtins[1:6]} = Inferred(class(builtins[int@{1:6}]))
            #variables = {NameError: {builtins[4:6]}, int: {builtins[1:6]}}
            #raise = {}
            #return = Inferred(None)
        builtins[NameError@{4:6}]:
            #variables = {}
            #raise = {}
            #return = Inferred(None)
        builtins[int@{1:6}][__add__@{2:8}]:
            self@{builtins[int@{1:6}][__add__@{2:8}][2:16]} = Inferred(Any)
            value@{builtins[int@{1:6}][__add__@{2:8}][2:22]} = Specified(@class(builtins[int@{1:6}]))
            #variables = {self: {builtins[int@{1:6}][__add__@{2:8}][2:16]}, value: {builtins[int@{1:6}][__add__@{2:8}][2:22]}}
            #raise = {}
            #return = Specified(@class(builtins[int@{1:6}]))
        builtins[int@{1:6}]:
            __add__@{builtins[int@{1:6}][2:8]} = Inferred(function(builtins[int@{1:6}][__add__@{2:8}]))
            #variables = {__add__: {builtins[int@{1:6}][2:8]}}
            #raise = {}
            #return = Inferred(None)
        "##};

        let module_loader = TestModuleLoader {
            modules: HashMap::from_iter([(BUILTINS_MODULE, TEST_BUILTINS.to_owned())]),
        };
        let dependent_graph = analyse_program(&module_loader, [].into_iter());

        let solver = ModuleConstraintSolver::new(&dependent_graph);

        let analysis_state = dependencies_analysis(&solver, &mut LogAnalysisObserver::default())
            .expect("analysis should work");

        let actual_expressions = format!("{:#}", analysis_state.program_evaluation);

        assert_eq!(
            expected_expressions, actual_expressions,
            "{actual_expressions}"
        );
    }

    #[rstest]
    #[case::simple_if_statement(
        indoc! {r##"
        x = True

        if x:
            a = 42
        else:
            a = 67

        b = a
        "##},
        indoc! {r##"
        module:
            a@{module[4:4]} = Inferred(42)
            b@{module[8:0]} = Inferred(42)
            x@{module[1:0]} = Inferred(True)
            #variables = {a: {module[4:4]}, b: {module[8:0]}, x: {module[1:0]}}
            #raise = {}
            #return = Inferred(None)
        "##},
    )]
    #[case::simple_while_statement(
        indoc! {r##"
        a = 0

        while a < 5:
            a = a + 1

        b = a
        "##},
        indoc! {r##"
        module:
            a@{module[1:0]} = Inferred(0)
            a@{module[4:4]} = Inferred(@class(builtins[int@{1:6}]))
            b@{module[6:0]} = Inferred(@class(builtins[int@{1:6}]))
            #variables = {a: {module[1:0], module[4:4]}, b: {module[6:0]}}
            #raise = {Exception(type=Inferred(Any), origin=Unknown)}
            #return = Inferred(None)
        "##},
    )]
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a: int, b: int) -> int:
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        module:
            add_two@{module[1:4]} = Inferred(function(module[add_two@{1:4}]))
            result@{module[4:0]} = Inferred(@class(builtins[int@{1:6}]))
            #variables = {add_two: {module[1:4]}, result: {module[4:0]}}
            #raise = {}
            #return = Inferred(None)
        module[add_two@{1:4}]:
            a@{module[add_two@{1:4}][1:12]} = Specified(@class(builtins[int@{1:6}]))
            b@{module[add_two@{1:4}][1:20]} = Specified(@class(builtins[int@{1:6}]))
            #variables = {a: {module[add_two@{1:4}][1:12]}, b: {module[add_two@{1:4}][1:20]}}
            #raise = {}
            #return = Specified(@class(builtins[int@{1:6}]))
        "##},
    )]
    #[case::simple_class_attribute_access(
        indoc! {r##"
        class A:
            b = 5

        result = A.b
        "##},
        indoc! {r##"
        module:
            A@{module[1:6]} = Inferred(class(module[A@{1:6}]))
            result@{module[4:0]} = Inferred(5)
            #variables = {A: {module[1:6]}, result: {module[4:0]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}]:
            b@{module[A@{1:6}][2:4]} = Inferred(5)
            #variables = {b: {module[A@{1:6}][2:4]}}
            #raise = {}
            #return = Inferred(None)
        "##},
    )]
    #[case::simple_attribute_access(
        indoc! {r##"
        class A:
            b = 5

        a = A()
        result = a.b
        "##},
        indoc! {r##"
        module:
            A@{module[1:6]} = Inferred(class(module[A@{1:6}]))
            a@{module[4:0]} = Inferred(@class(module[A@{1:6}]))
            result@{module[5:0]} = Inferred(5)
            #variables = {A: {module[1:6]}, a: {module[4:0]}, result: {module[5:0]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}]:
            b@{module[A@{1:6}][2:4]} = Inferred(5)
            #variables = {b: {module[A@{1:6}][2:4]}}
            #raise = {}
            #return = Inferred(None)
        "##},
    )]
    #[case::simple_class_function_access(
        indoc! {r##"
        class A:
            def foo():
                return 5

        result = A.foo
        "##},
        indoc! {r##"
        module:
            A@{module[1:6]} = Inferred(class(module[A@{1:6}]))
            result@{module[5:0]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #variables = {A: {module[1:6]}, result: {module[5:0]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}]:
            foo@{module[A@{1:6}][2:8]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #variables = {foo: {module[A@{1:6}][2:8]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}][foo@{2:8}]:
            #variables = {}
            #raise = {}
            #return = Inferred(5)
        "##},
    )]
    #[case::simple_method_access(
        indoc! {r##"
        class A:
            def foo():
                return 5

        a = A()
        result = a.foo
        "##},
        indoc! {r##"
        module:
            A@{module[1:6]} = Inferred(class(module[A@{1:6}]))
            a@{module[5:0]} = Inferred(@class(module[A@{1:6}]))
            result@{module[6:0]} = Inferred(method(class(module[A@{1:6}])[], function(module[A@{1:6}][foo@{2:8}])))
            #variables = {A: {module[1:6]}, a: {module[5:0]}, result: {module[6:0]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}]:
            foo@{module[A@{1:6}][2:8]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #variables = {foo: {module[A@{1:6}][2:8]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{1:6}][foo@{2:8}]:
            #variables = {}
            #raise = {}
            #return = Inferred(5)
        "##},
    )]
    #[case::hard_function_call(
        indoc! {r##"
        def foo():
            return CONST

        result = foo()

        CONST = 5
        "##},
        indoc! {r##"
        module:
            CONST@{module[6:0]} = Inferred(5)
            foo@{module[1:4]} = Inferred(function(module[foo@{1:4}]))
            result@{module[4:0]} = Inferred(5)
            #variables = {CONST: {module[6:0]}, foo: {module[1:4]}, result: {module[4:0]}}
            #raise = {}
            #return = Inferred(None)
        module[foo@{1:4}]:
            #variables = {}
            #raise = {}
            #return = Inferred(5)
        "##},  // TODO: fix when possible
    )]
    #[case::forward_reference_function_call(
        indoc! {r##"
        def foo():
            return CONST

        CONST = 5

        result = foo()
        "##},
        indoc! {r##"
        module:
            CONST@{module[4:0]} = Inferred(5)
            foo@{module[1:4]} = Inferred(function(module[foo@{1:4}]))
            result@{module[6:0]} = Inferred(5)
            #variables = {CONST: {module[4:0]}, foo: {module[1:4]}, result: {module[6:0]}}
            #raise = {}
            #return = Inferred(None)
        module[foo@{1:4}]:
            #variables = {}
            #raise = {}
            #return = Inferred(5)
        "##},
    )]
    #[case::forward_annotation(
        indoc! {r##"
        a: A

        class A:
            b = 5
        "##},
        indoc! {r##"
        module:
            A@{module[3:6]} = Inferred(class(module[A@{3:6}]))
            a@{module[1:0]} = Inferred(@class(module[A@{3:6}])) ⊔ #deferred{#annotated(A)}
            #variables = {A: {module[3:6]}}
            #raise = {}
            #return = Inferred(None)
        module[A@{3:6}]:
            b@{module[A@{3:6}][4:4]} = Inferred(5)
            #variables = {b: {module[A@{3:6}][4:4]}}
            #raise = {}
            #return = Inferred(None)
        "##},
    )]
    #[case::argument_inference(
        indoc! {r##"
        def foo(x):
            return x

        result = foo(5)
        "##},
        indoc! {r##"
        module:
            foo@{module[1:4]} = Inferred(function(module[foo@{1:4}]))
            result@{module[4:0]} = Inferred(5)
            #variables = {foo: {module[1:4]}, result: {module[4:0]}}
            #raise = {}
            #return = Inferred(None)
        module[foo@{1:4}]:
            x@{module[foo@{1:4}][1:8]} = Inferred(5)
            #variables = {x: {module[foo@{1:4}][1:8]}}
            #raise = {}
            #return = Inferred(5)
        "##},
    )]
    fn test_constraints_solving(#[case] source: &str, #[case] expected_expressions: &str) {
        init_logger();

        let module_name = SmolStr::new_static("module");
        let module_loader = TestModuleLoader {
            modules: HashMap::from_iter([
                (module_name.clone(), source.to_string()),
                (BUILTINS_MODULE, TEST_BUILTINS.to_owned()),
            ]),
        };

        let dependent_graph = analyse_program(&module_loader, std::iter::once(module_name.clone()));

        let solver = ModuleConstraintSolver::new(&dependent_graph);

        let mut analysis_state =
            dependencies_analysis(&solver, &mut LogAnalysisObserver::default())
                .expect("analysis should work");

        analysis_state.program_evaluation.states = analysis_state
            .program_evaluation
            .states
            .into_iter()
            .filter(|(namespace, _)| *namespace.module_name() == module_name)
            .collect();

        let actual_expressions = format!("{:#}", analysis_state.program_evaluation);

        assert_eq!(
            expected_expressions, actual_expressions,
            "{actual_expressions}"
        );
    }
}
