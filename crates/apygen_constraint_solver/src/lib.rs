use crate::analysis::abstract_state::{AbstractState, AbstractStateProxy};
use crate::analysis::fmt::fmt_set;
use crate::analysis::lattice::Join;
use crate::analysis::{DependencyGraphAnalyser, DummyAnalysisObserver, GraphAnalyser, analysis};
use crate::calls::Arguments;
use crate::constraint_graph::expressions::{
    BinaryOperator, Expression, ExpressionAnnotated, ExpressionAttribute, ExpressionBinary,
    ExpressionCall, ExpressionClass, ExpressionFunction, ExpressionImport, ExpressionSubscript,
    ExpressionUnary, ExpressionVariableDefinition, ExpressionVariableReference, Namespace, SmolStr,
};
use crate::constraint_graph::graph::Graph;
use crate::constraint_graph::graph::dot::DiGraphDot;
use crate::constraint_graph::{
    Constraint, ConstraintGraph, ConstraintNode, Guard, ModuleDependentGraph,
};
use crate::expressions::literal_class::method_resolution_order;
use crate::expressions::{PyEffects, PyTypeEval, gen_bool_value, type_literal};
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
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;
use std::fmt::{Debug, Display, Formatter};
use std::sync::Arc;
use thiserror::Error;

pub use apygen_analysis as analysis;
pub use apygen_constraint_graph as constraint_graph;
pub use apygen_identifiers as identifiers;
pub use apygen_inference as inference;
pub use apygen_primitives as primitives;
pub use imbl;

pub mod calls;
pub mod expressions;

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Join)]
pub struct EvaluationState {
    pub types: imbl::OrdMap<Arc<Expression>, Deferred<Sourced<Type>, Expression>>,
    pub return_value: Deferred<Sourced<Type>, Expression>,
    pub raised_exceptions: Deferred<Sourced<RaisedExceptions>, Expression>,
    pub defined_variables: DefinedVariables,
    pub calls:
        imbl::OrdMap<Arc<Namespace>, imbl::OrdMap<QualifiedLocation, imbl::OrdSet<Arguments>>>,
    pub definitions: imbl::OrdSet<(Arc<Namespace>, bool)>,
}

impl EvaluationState {
    pub fn get_variable_type(
        &self,
        variable_name: &SmolStr,
        locations: &imbl::OrdSet<(Arc<Namespace>, Location)>,
    ) -> Option<Deferred<Sourced<Type>, Expression>> {
        let mut ty = None;
        for (namespace, location) in locations {
            let variable = Expression::VariableDefinition(ExpressionVariableDefinition::new(
                NamedQualifiedLocation::new(
                    variable_name.clone(),
                    location.clone(),
                    namespace.clone(),
                ),
            ));
            ty = ty.join(&self.types.get(&variable).cloned());
        }
        ty
    }
}

impl Display for EvaluationState {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            for (expression, deferred_ty) in &self.types {
                writeln!(f, "{} = {}", expression, deferred_ty)?;
            }
            writeln!(f, "#variables = {}", self.defined_variables)?;
            writeln!(f, "#raise = {}", self.raised_exceptions)?;
            writeln!(f, "#return = {}", self.return_value)
        } else {
            f.write_str("(evaluations: ")?;
            fmt_set(f, self.types.iter(), |f, (expression, eval)| {
                write!(f, "{}: {}", expression, eval)
            })?;
            write!(
                f,
                ", return: {}, raised: {}, defined_variables: {})",
                self.return_value, self.raised_exceptions, self.defined_variables
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

    fn raised_exceptions(&self) -> &Deferred<Sourced<RaisedExceptions>, Self::Expression> {
        &self.raised_exceptions
    }

    fn return_value(&self) -> &Deferred<Sourced<Type>, Self::Expression> {
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

impl<N: Clone + Ord, S: Clone> AbstractState for SolverState<N, S> {
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
    pub current_expression: Option<Expression>,
}

impl<'a> ExpressionEvaluator<'a> {
    pub fn new(mode: EvaluatorMode, namespace: &'a Namespace) -> Self {
        Self {
            mode,
            namespace,
            current_expression: None,
        }
    }

    pub fn with_namespace(&self, namespace: &'a Namespace) -> Self {
        Self::new(self.mode, namespace)
    }

    pub fn with_mode(&self, mode: EvaluatorMode) -> Self {
        Self::new(mode, self.namespace)
    }

    pub fn extract_deferred<T: Clone>(
        deferred: &Deferred<Sourced<T>, Expression>,
    ) -> Result<T, EvaluationError> {
        match deferred.as_value() {
            Some(sourced) => Ok(sourced.data.clone()),
            None => Err(EvaluationError::Deferred),
        }
    }

    pub fn find_type(
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
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

    pub fn evaluate_expression_variable_definition(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_variable_definition: &ExpressionVariableDefinition,
    ) -> Result<PyTypeEval, EvaluationError> {
        let namespace = expression_variable_definition.namespace();

        let Some(evaluation_state) = abstract_state.get(namespace) else {
            return Err(EvaluationError::NamespaceReferenceError(
                namespace.as_ref().clone(),
            ));
        };

        let exists = evaluation_state
            .defined_variables
            .names
            .get(expression_variable_definition.name())
            .map(|locations| {
                locations.contains(&(
                    namespace.clone(),
                    expression_variable_definition.location().clone(),
                ))
            })
            .unwrap_or(false);

        if exists {
            Ok(PyTypeEval::with_default_effects(Self::extract_deferred(
                &evaluation_state
                    .types
                    .get(&Expression::VariableDefinition(
                        expression_variable_definition.clone(),
                    ))
                    .cloned()
                    .unwrap_or_default(),
            )?))
        } else {
            Ok(PyTypeEval::raise(Exception::new(
                Arc::new(Self::find_type(
                    abstract_state,
                    &BUILTINS_MODULE,
                    &SmolStr::new_static("NameError"),
                )?),
                ExceptionOrigin::Specified, // TODO: fix origin
            )))
        }
    }

    pub fn evaluate_expression_variable_reference(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_variable_reference: &ExpressionVariableReference,
    ) -> Result<PyTypeEval, EvaluationError> {
        let Some(evaluation_state) = abstract_state.get(self.namespace) else {
            return Err(EvaluationError::NamespaceReferenceError(
                self.namespace.clone(),
            ));
        };

        if let Some(deferred_ty) =
            evaluation_state.get_attribute(&expression_variable_reference.name)
        {
            return Ok(PyTypeEval::with_default_effects(Self::extract_deferred(
                &deferred_ty,
            )?));
        }

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

        Ok(PyTypeEval::raise(Exception::new(
            Arc::new(Self::find_type(
                abstract_state,
                &BUILTINS_MODULE,
                &SmolStr::new_static("NameError"),
            )?),
            ExceptionOrigin::Specified, // TODO: fix origin
        )))
    }

    pub fn evaluate_expression_annotated(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_annotated: &ExpressionAnnotated,
    ) -> Result<PyTypeEval, EvaluationError> {
        let annotation_eval = self
            .with_mode(EvaluatorMode::Annotation)
            .evaluate_expression(abstract_state, &expression_annotated.annotation)?;

        let Type::Literal(type_literal) = annotation_eval.value else {
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

        Ok(PyTypeEval::with_default_effects(Type::Instance(
            TypeInstance {
                base,
                arguments: imbl::Vector::new(),
            },
        )))
    }

    pub fn evaluate_expression_function(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_function: &ExpressionFunction,
    ) -> Result<PyTypeEval, EvaluationError> {
        let function_namespace =
            Namespace::NamedProgramEntity(expression_function.program_entity.clone());

        Ok(PyTypeEval::new(
            Type::new_literal(TypeLiteral::Function(LiteralFunction {
                value: Arc::new(FunctionType {
                    program_entity: expression_function.program_entity.clone(),
                    generics: Default::default(),
                    parameters: Default::default(),
                    is_async: expression_function.is_async,
                }),
            })),
            PyEffects::new()
                .with_definitions(imbl::OrdSet::unit((Arc::new(function_namespace), false))),
        ))
    }

    pub fn evaluate_expression_class(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_class: &ExpressionClass,
    ) -> Result<PyTypeEval, EvaluationError> {
        let class_namespace =
            Namespace::NamedProgramEntity(expression_class.program_entity.clone());

        Ok(PyTypeEval::new(
            Type::new_literal(TypeLiteral::Class(LiteralClass {
                value: Arc::new(ClassType {
                    program_entity: expression_class.program_entity.clone(),
                    generics: Default::default(),
                    bases: Default::default(),
                    keyword_arguments: Default::default(),
                    is_abstract: false,
                }),
            })),
            PyEffects::new()
                .with_definitions(imbl::OrdSet::unit((Arc::new(class_namespace), true))),
        ))
    }

    pub fn evaluate_expression_import(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_import: &ExpressionImport,
    ) -> Result<PyTypeEval, EvaluationError> {
        let namespace = Namespace::Module(expression_import.module.clone());

        if abstract_state.contains(&namespace) {
            Ok(PyTypeEval::with_default_effects(Type::new_literal(
                TypeLiteral::ImportedModule(LiteralImportedModule {
                    value: Arc::new(ImportedModuleType {
                        module: expression_import.module.clone(),
                    }),
                }),
            )))
        } else {
            Err(EvaluationError::Deferred) // TODO: Add import exception when possible
        }
    }

    /// References: https://docs.python.org/3/howto/descriptor.html
    fn evaluate_attributes(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        value_ty: &Type,
        name: &SmolStr,
        instance_arguments: Option<&imbl::Vector<Arc<Type>>>,
    ) -> Result<PyTypeEval, EvaluationError> {
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
                            Arc::new(Type::Any),
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

                        let mut ty = Self::extract_deferred(&deferred_ty)?;

                        if let Type::Literal(type_literal) = &ty {
                            if let TypeLiteral::Function(literal_function) = type_literal.as_ref() {
                                if let Some(arguments) = instance_arguments {
                                    ty = Type::new_literal(TypeLiteral::Method(LiteralMethod {
                                        class: class.value.clone(),
                                        function: literal_function.value.clone(),
                                        arguments: arguments.clone(),
                                    }));
                                }
                            }
                        };

                        return Ok(PyTypeEval::with_default_effects(ty));
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
            _ => Err(EvaluationError::Deferred), // TODO: add missing cases
        }
    }

    pub fn evaluate_expression_attribute(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_attribute: &ExpressionAttribute,
    ) -> Result<PyTypeEval, EvaluationError> {
        let mut effects = PyEffects::new();

        let value_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_attribute.value)?
        );

        self.evaluate_attributes(
            abstract_state,
            &value_ty,
            &expression_attribute.attribute,
            None,
        )
    }

    pub fn evaluate_expression_subscript(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_subscript: &ExpressionSubscript,
    ) -> Result<PyTypeEval, EvaluationError> {
        let mut effects = PyEffects::new();

        let value_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_subscript.value)?
        );
        let get_item = self.evaluate_attributes(
            abstract_state,
            &value_ty,
            &SmolStr::new_static("__getitem__"),
            None,
        )?;
        let slice_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_subscript.slice)?
        );

        let ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_call(
                abstract_state,
                &get_item.value,
                Arguments::new().add_positional_argument(Arc::new(slice_ty))
            )?
        );

        Ok(PyTypeEval::new(ty, effects))
    }

    pub fn evaluate_call(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        ty: &Type,
        arguments: Arguments,
    ) -> Result<PyTypeEval, EvaluationError> {
        let Type::Literal(literal) = ty else {
            return Err(EvaluationError::Deferred); // TODO: add support for unions, etc
        };

        match literal.as_ref() {
            TypeLiteral::Function(literal_function) => {
                let function_namespace =
                    Namespace::NamedProgramEntity(literal_function.value.program_entity.clone());

                let Some(evaluation_state) = abstract_state.get(&function_namespace) else {
                    return Err(EvaluationError::Deferred);
                };

                Ok(PyTypeEval::new(
                    Self::extract_deferred(&evaluation_state.return_value)?,
                    PyEffects::new()
                        .with_exceptions(Self::extract_deferred(
                            &evaluation_state.raised_exceptions,
                        )?)
                        .with_calls(imbl::OrdMap::unit(
                            Arc::new(function_namespace),
                            imbl::OrdSet::new(),
                        )),
                ))
            }
            TypeLiteral::Method(literal_method) => self.evaluate_call(
                abstract_state,
                &Type::Literal(Arc::new(TypeLiteral::Function(LiteralFunction {
                    value: literal_method.function.clone(),
                }))),
                arguments.with_self(Arc::new(Type::Literal(Arc::new(TypeLiteral::Class(
                    LiteralClass {
                        value: literal_method.class.clone(),
                    },
                ))))),
            ),
            TypeLiteral::Class(literal_class) => Ok(PyTypeEval::with_default_effects(
                Type::Instance(TypeInstance {
                    base: Base::Class(literal_class.clone()),
                    arguments: imbl::Vector::new(),
                }),
            )),
            _ => Err(EvaluationError::Deferred), // TODO: add support for classes, etc
        }
    }

    pub fn evaluate_expression_call(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_call: &ExpressionCall,
    ) -> Result<PyTypeEval, EvaluationError> {
        let mut effects = PyEffects::new();

        let ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_call.target)?
        );

        let mut arguments = Arguments::new();

        for argument in &expression_call.positional_arguments {
            let argument_ty = pytype_consume_or_return_ok!(
                effects,
                self.evaluate_expression(abstract_state, &argument)?
            );

            arguments.positional.push(Arc::new(argument_ty));
        }
        for keyword_argument in &expression_call.keyword_arguments {
            if let Some(name) = &keyword_argument.name {
                let keyword_argument_ty = pytype_consume_or_return_ok!(
                    effects,
                    self.evaluate_expression(abstract_state, &keyword_argument.value)?
                );

                arguments
                    .keyword
                    .insert(name.clone(), Arc::new(keyword_argument_ty));
            }
        }

        self.evaluate_call(abstract_state, &ty, arguments)
    }

    pub fn evaluate_expression_unary(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_unary: &ExpressionUnary,
    ) -> Result<PyTypeEval, EvaluationError> {
        let mut effects = PyEffects::new();

        let operand_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_unary.operand)?
        );

        let ty = match operand_ty {
            Type::Literal(type_literal) => {
                pytype_consume_or_return_ok!(
                    effects,
                    type_literal::call_unary_op(type_literal.as_ref(), expression_unary.operator)
                )
            }
            Type::Never | Type::NoReturn => unreachable!("operand_ty should not be unreachable"),
            _ => return Err(EvaluationError::Deferred), // TODO: add other cases
        };

        Ok(PyTypeEval::new(ty, effects))
    }

    pub fn evaluate_binary_operation(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        left_ty: &Type,
        operator: BinaryOperator,
        right_ty: &Type,
    ) -> Result<PyTypeEval, EvaluationError> {
        match (left_ty, right_ty) {
            (Type::Literal(left), Type::Literal(right)) => Ok(type_literal::call_binary_op(
                left.as_ref(),
                operator,
                right.as_ref(),
            )),
            (Type::Instance(_), _) => {
                let mut effects = PyEffects::new();

                let Some(method_name) = operator.method_name() else {
                    return Err(EvaluationError::Deferred); // TODO: fix
                };

                let method = pytype_consume_or_return_ok!(
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
                        &method,
                        Arguments::new().add_positional_argument(Arc::new(right_ty.clone())),
                    )?
                );

                Ok(PyTypeEval::new(return_type, effects))
            }
            (_, Type::Instance(_)) => {
                let mut effects = PyEffects::new();

                let Some(method_name) = operator.method_name() else {
                    return Err(EvaluationError::Deferred); // TODO: fix
                };

                let method = pytype_consume_or_return_ok!(
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
                        &method,
                        Arguments::new().add_positional_argument(Arc::new(left_ty.clone())),
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
            _ => Err(EvaluationError::Deferred), // TODO: add support for the rest
        }
    }

    pub fn evaluate_expression_binary(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression_binary: &ExpressionBinary,
    ) -> Result<PyTypeEval, EvaluationError> {
        let mut effects = PyEffects::new();

        let left_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_binary.left)?
        );
        let right_ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_expression(abstract_state, &expression_binary.right)?
        );

        let ty = pytype_consume_or_return_ok!(
            effects,
            self.evaluate_binary_operation(
                abstract_state,
                &left_ty,
                expression_binary.operator,
                &right_ty
            )?
        );

        Ok(PyTypeEval::new(ty, effects))
    }

    pub fn evaluate_expression(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expression: &Expression,
    ) -> Result<PyTypeEval, EvaluationError> {
        if let Some(expression_eval) = abstract_state
            .get(self.namespace)
            .and_then(|state| state.types.get(expression))
            .cloned()
        {
            if let Some(current_expression) = &self.current_expression {
                if current_expression == expression && !expression_eval.expressions.is_empty() {
                    return Err(EvaluationError::Deferred);
                }
            }
            if self.current_expression == None {
                self.current_expression = Some(expression.clone());
            }
            let eval = self.evaluate_expressions(
                abstract_state,
                expression_eval
                    .expressions
                    .iter()
                    .map(|expression| expression.as_ref()),
            )?;
            if self.current_expression.as_ref() == Some(expression) {
                self.current_expression = None;
            }
            return Ok(PyTypeEval::new(
                expression_eval.value.data.join(&eval.value),
                eval.effects,
            ));
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
            Expression::Override(_) => Err(EvaluationError::Deferred),
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
                Type::new_integer_literal(literal_integer.clone()),
            )),
            Expression::LiteralFloat(literal_float) => Ok(PyTypeEval::with_default_effects(
                Type::new_float_literal(literal_float.clone()),
            )),
            Expression::LiteralComplex(literal_complex) => Ok(PyTypeEval::with_default_effects(
                Type::new_complex_literal(literal_complex.clone()),
            )),
            Expression::LiteralString(literal_string) => Ok(PyTypeEval::with_default_effects(
                Type::new_string_literal(literal_string.clone()),
            )),
            Expression::LiteralBytes(literal_bytes) => Ok(PyTypeEval::with_default_effects(
                Type::new_bytes_literal(literal_bytes.clone()),
            )),
            Expression::LiteralBoolean(literal_boolean) => Ok(PyTypeEval::with_default_effects(
                Type::new_boolean_literal(literal_boolean.clone()),
            )),
            Expression::LiteralNone => Ok(PyTypeEval::with_default_effects(Type::new_literal(
                TypeLiteral::None,
            ))),
            Expression::LiteralEllipsis => Ok(PyTypeEval::with_default_effects(Type::new_literal(
                TypeLiteral::Ellipsis,
            ))),
        }
    }

    pub fn evaluate_expressions<'e>(
        &mut self,
        abstract_state: &mut dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
        expressions: impl IntoIterator<Item = &'e Expression>,
    ) -> Result<PyTypeEval, EvaluationError> {
        let mut eval = PyTypeEval::never();

        for expression in expressions {
            eval = eval.join(&self.evaluate_expression(abstract_state, expression)?);
        }

        Ok(eval)
    }
}

pub struct ConstraintSolver<'s> {
    pub namespace: &'s Namespace,
    pub constraint_graph: &'s ConstraintGraph,
    pub program_evaluation: &'s dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
}

impl<'s> ConstraintSolver<'s> {
    pub fn new(
        namespace: &'s Namespace,
        constraint_graph: &'s ConstraintGraph,
        program_evaluation: &'s dyn AbstractState<Key = Namespace, AbstractValue = EvaluationState>,
    ) -> Self {
        Self {
            namespace,
            constraint_graph,
            program_evaluation,
        }
    }

    pub fn evaluator(&self, mode: EvaluatorMode) -> ExpressionEvaluator<'_> {
        ExpressionEvaluator::new(mode, self.namespace)
    }
}

impl<'s> GraphAnalyser for ConstraintSolver<'s> {
    type Node = ConstraintNode;
    type AbstractState =
        AbstractStateProxy<'s, Namespace, EvaluationState, ProgramEvaluation<EvaluationState>>;
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
        let mut program_evaluation = analysis_state.get_clone(node).unwrap_or_else(|| {
            AbstractStateProxy::new(
                self.program_evaluation,
                ProgramEvaluation::new(imbl::OrdMap::unit(
                    self.namespace.clone(),
                    EvaluationState::default(),
                )),
            )
        });

        match &node {
            ConstraintNode::Entry => {
                let specification = &self.constraint_graph.specification;

                let arguments: BTreeMap<_, _> = specification
                    .arguments
                    .iter()
                    .map(|(variable, expressions)| {
                        let ty = if let Ok(eval) = self
                            .evaluator(EvaluatorMode::Normal)
                            .evaluate_expressions(&mut program_evaluation, expressions)
                        {
                            Deferred::known(Sourced::specified(eval.value))
                        } else {
                            Deferred::unknown(
                                expressions
                                    .iter()
                                    .map(|expression| Arc::new(expression.clone()))
                                    .collect(),
                            )
                        };
                        (variable.clone(), ty)
                    })
                    .collect();

                let raised_exceptions: BTreeSet<_> = specification
                    .exceptions
                    .iter()
                    .map(|expression| {
                        if let Ok(eval) = self
                            .evaluator(EvaluatorMode::Normal)
                            .evaluate_expression(&mut program_evaluation, expression)
                        {
                            Deferred::known(Sourced::specified(RaisedExceptions::raise(
                                Exception::new(Arc::new(eval.value), ExceptionOrigin::Specified),
                            )))
                        } else {
                            Deferred::unknown(imbl::OrdSet::unit(Arc::new(expression.clone())))
                        }
                    })
                    .collect();

                let return_ty = if let Ok(eval) = self
                    .evaluator(EvaluatorMode::Normal)
                    .evaluate_expressions(&mut program_evaluation, &specification.return_type)
                {
                    Deferred::known(Sourced::specified(eval.value))
                } else {
                    Deferred::unknown(
                        specification
                            .return_type
                            .iter()
                            .map(|expression| Arc::new(expression.clone()))
                            .collect(),
                    )
                };

                let evaluation_state =
                    program_evaluation.get_or_insert_default(self.namespace.clone());

                for (variable, ty) in arguments {
                    evaluation_state.defined_variables.names.insert(
                        variable.named_qualified_location.name.clone(),
                        imbl::OrdSet::unit((
                            variable.named_qualified_location.namespace.clone(),
                            variable.named_qualified_location.location.clone(),
                        )),
                    );

                    evaluation_state.types.insert(
                        Arc::new(Expression::VariableDefinition(variable.clone())),
                        ty,
                    );
                }

                if !specification.exceptions.is_empty() {
                    for exceptions in &raised_exceptions {
                        evaluation_state.raised_exceptions =
                            evaluation_state.raised_exceptions.join(exceptions);
                    }
                }

                if !specification.return_type.is_empty() {
                    evaluation_state.return_value = return_ty;
                }
            }
            ConstraintNode::Constraint { location, .. } => {
                if let Some(constraints) = self.constraint_graph.nodes.get(node) {
                    for constraint in constraints {
                        match constraint {
                            Constraint::Type(type_constraint) => {
                                let (ty, raised_exceptions, calls, definitions) = match self
                                    .evaluator(EvaluatorMode::Normal)
                                    .evaluate_expression(
                                        &mut program_evaluation,
                                        &type_constraint.left,
                                    ) {
                                    Ok(type_eval) => (
                                        Deferred::known(Sourced::inferred(type_eval.value)),
                                        Deferred::known(Sourced::inferred(
                                            type_eval.effects.exceptions,
                                        )),
                                        type_eval.effects.calls,
                                        type_eval.effects.definitions,
                                    ),
                                    Err(_) => (
                                        Deferred::unknown(imbl::OrdSet::unit(
                                            type_constraint.left.clone(),
                                        )),
                                        Deferred::unknown(imbl::OrdSet::unit(
                                            type_constraint.left.clone(),
                                        )),
                                        imbl::OrdMap::new(),
                                        imbl::OrdSet::new(),
                                    ),
                                };

                                let evaluation_state = program_evaluation
                                    .get_or_insert_default(self.namespace.clone());

                                evaluation_state
                                    .types
                                    .entry(type_constraint.right.clone())
                                    .and_modify(|previous_eval| {
                                        *previous_eval = previous_eval.join(&ty)
                                    })
                                    .or_insert(ty);
                                evaluation_state.raised_exceptions =
                                    evaluation_state.raised_exceptions.join(&raised_exceptions);
                                if let Some(location) = location {
                                    for (call_namespace, arguments) in calls {
                                        evaluation_state.calls =
                                            evaluation_state.calls.join(&imbl::OrdMap::unit(
                                                call_namespace,
                                                imbl::OrdMap::unit(
                                                    QualifiedLocation::new(
                                                        location.clone(),
                                                        Arc::new(self.namespace.clone()),
                                                    ),
                                                    arguments,
                                                ),
                                            ));
                                    }
                                    for definition in definitions {
                                        evaluation_state.definitions.insert(definition);
                                    }
                                }
                            }
                            Constraint::Return(return_constraint) => {
                                let (ty, raised_exceptions) = match self
                                    .evaluator(EvaluatorMode::Normal)
                                    .evaluate_expression(
                                        &mut program_evaluation,
                                        &return_constraint.expression,
                                    ) {
                                    Ok(type_eval) => (
                                        Deferred::known(Sourced::inferred(type_eval.value)),
                                        Deferred::known(Sourced::inferred(
                                            type_eval.effects.exceptions,
                                        )),
                                    ),
                                    Err(_) => (
                                        Deferred::unknown(imbl::OrdSet::unit(
                                            return_constraint.expression.clone(),
                                        )),
                                        Deferred::unknown(imbl::OrdSet::unit(
                                            return_constraint.expression.clone(),
                                        )),
                                    ),
                                };

                                let evaluation_state = program_evaluation
                                    .get_or_insert_default(self.namespace.clone());

                                if !matches!(
                                    evaluation_state.return_value.value.source,
                                    Source::Specified
                                ) {
                                    evaluation_state.return_value = ty;
                                }
                                evaluation_state.raised_exceptions =
                                    raised_exceptions.join(&raised_exceptions);
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
                            }
                        }
                    }
                }
            }
            _ => {}
        }

        Ok(program_evaluation)
    }

    fn update_abstract_state(
        &self,
        _analysis_state: &Self::AnalysisState,
        from: &Self::Node,
        to: &Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error> {
        let mut new_abstract_state = abstract_state.clone();

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
                Guard::IsTrue(expression) => {
                    let eval = self
                        .evaluator(EvaluatorMode::Normal)
                        .evaluate_expression(&mut new_abstract_state, expression);

                    if let Ok(type_eval) = eval {
                        if let Some(bool_value) = gen_bool_value(&type_eval.value) {
                            if !bool_value {
                                continue;
                            }
                        }
                    }
                    should_ignore = false;
                }
                Guard::IsFalse(expression) => {
                    let eval = self
                        .evaluator(EvaluatorMode::Normal)
                        .evaluate_expression(&mut new_abstract_state, expression);

                    if let Ok(type_eval) = eval {
                        if let Some(bool_value) = gen_bool_value(&type_eval.value) {
                            if bool_value {
                                continue;
                            }
                        }
                    }
                    should_ignore = false;
                }
                Guard::Succeed(expression) => {
                    let eval = self
                        .evaluator(EvaluatorMode::Normal)
                        .evaluate_expression(&mut new_abstract_state, expression);

                    if let Ok(type_eval) = eval {
                        if is_type_unreachable!(type_eval.value) {
                            continue;
                        }
                    }
                    should_ignore = false;
                }
                Guard::Raise { expression, .. } => {
                    let eval = self
                        .evaluator(EvaluatorMode::Normal)
                        .evaluate_expression(&mut new_abstract_state, expression);

                    let evaluation_state =
                        new_abstract_state.get_or_insert_default(self.namespace.clone());

                    if let Ok(type_eval) = eval {
                        evaluation_state.raised_exceptions.value = evaluation_state
                            .raised_exceptions
                            .value
                            .join(&Sourced::inferred(type_eval.effects.exceptions));
                    } else {
                        evaluation_state
                            .raised_exceptions
                            .expressions
                            .insert(expression.clone());
                    }
                    should_ignore = false;
                }
            }
        }

        if should_ignore {
            Ok(None)
        } else if matches!(to, ConstraintNode::ExceptionExit) {
            if let Some(program_evaluation) = new_abstract_state.get_mut(self.namespace) {
                program_evaluation.types.clear();
                program_evaluation.return_value = Deferred::default();
                program_evaluation.defined_variables.names.clear();
            }
            Ok(Some(new_abstract_state))
        } else {
            Ok(Some(new_abstract_state))
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
        left: &Self::AbstractState,
        right: &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error> {
        assert!(std::ptr::addr_eq(
            left.abstract_state,
            self.program_evaluation
        ));
        assert!(std::ptr::addr_eq(
            right.abstract_state,
            self.program_evaluation
        ));

        let mut new_abstract_state =
            AbstractStateProxy::new(self.program_evaluation, left.proxy.join(&right.proxy));

        if let Some(evaluation_state) = new_abstract_state.get(&self.namespace) {
            let new_evaluations = evaluation_state
                .types
                .clone()
                .into_iter()
                .map(|(expression, mut eval)| {
                    while eval.value.data.width() > WIDTH_LIMIT {
                        eval.value = match eval.value.data {
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

                    if eval.value.data.depth() > DEPTH_LIMIT {
                        eval.value = Sourced::inferred(Type::Any);
                    }

                    (expression, eval)
                })
                .collect();

            new_abstract_state
                .get_mut(&self.namespace)
                .expect("evaluation_state should exists")
                .types = new_evaluations;
        }

        Ok(new_abstract_state)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join, Default)]
pub struct NamespaceData {
    pub dependents: imbl::OrdSet<Namespace>,
    pub dependencies: imbl::OrdSet<Namespace>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Join)]
pub struct NamespaceDependencyGraph {
    nodes: imbl::OrdMap<Namespace, NamespaceData>,
    edges: imbl::OrdMap<
        (Namespace, Namespace),
        imbl::OrdMap<QualifiedLocation, imbl::OrdSet<Arguments>>,
    >,
}

impl NamespaceDependencyGraph {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Default for NamespaceDependencyGraph {
    fn default() -> Self {
        Self {
            nodes: imbl::OrdMap::default(),
            edges: imbl::OrdMap::default(),
        }
    }
}

impl NamespaceDependencyGraph {
    pub fn nodes(&self) -> &imbl::OrdMap<Namespace, NamespaceData> {
        &self.nodes
    }
    pub fn edges(
        &self,
    ) -> &imbl::OrdMap<
        (Namespace, Namespace),
        imbl::OrdMap<QualifiedLocation, imbl::OrdSet<Arguments>>,
    > {
        &self.edges
    }
    pub fn add_dependency(
        &mut self,
        dependency: Namespace,
        node: Namespace,
        calls: imbl::OrdMap<QualifiedLocation, imbl::OrdSet<Arguments>>,
    ) {
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
        let existing_calls = self.edges.entry((dependency, node)).or_default();
        *existing_calls = existing_calls.join(&calls);
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
    type EdgeData = imbl::OrdMap<QualifiedLocation, imbl::OrdSet<Arguments>>;

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
    constraint_graph: &ConstraintGraph,
    analysis_state: &mut ModuleConstraintSolverAnalysisState,
) -> Result<(), Infallible> {
    loop {
        let previous_evaluation_state = analysis_state.program_evaluation.get(namespace).cloned();

        let solver_state = analysis(
            &ConstraintSolver::new(
                &namespace,
                constraint_graph,
                &mut analysis_state.program_evaluation,
            ),
            &mut DummyAnalysisObserver::default(),
        )?;

        let evaluation_state =
            if let Some(program_evaluation) = solver_state.get(&ConstraintNode::TypeExit) {
                let mut evaluation_state = program_evaluation.get_clone_or_default(namespace);

                if let Some(exception_evaluation_state) = solver_state
                    .get(&ConstraintNode::ExceptionExit)
                    .and_then(|program_evaluation| program_evaluation.get(namespace))
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
                    .and_then(|program_evaluation| program_evaluation.get(namespace).cloned())
                    .unwrap_or_default()
            };

        let new_abstract_state = solver_state.get(&ConstraintNode::Exit).cloned(); // TODO: should always exist

        drop(solver_state);

        if let Some(new_abstract_state) = new_abstract_state {
            let proxy_states = new_abstract_state.proxy;
            analysis_state
                .program_evaluation
                .extend(&mut proxy_states.states.into_iter());
        }

        for (called_namespace, calls) in &evaluation_state.calls {
            analysis_state.namespace_dependency_graph.add_dependency(
                called_namespace.as_ref().clone(),
                namespace.clone(),
                calls.clone(),
            );
        }

        let evaluation_state: &EvaluationState = analysis_state
            .program_evaluation
            .insert(namespace.clone(), evaluation_state);

        if Some(evaluation_state) == previous_evaluation_state.as_ref() {
            break;
        }

        for (sub_namespace, subgraph) in &constraint_graph.subgraphs {
            analysis_state.namespace_dependency_graph.add_dependency(
                namespace.clone(),
                sub_namespace.as_ref().clone(),
                imbl::OrdMap::default(),
            );
            solve_namespace(sub_namespace, subgraph, analysis_state)?;
        }
    }

    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Join)]
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
        BTreeMap<ExpressionVariableDefinition, Deferred<Sourced<Type>, Expression>>,
    >;
    type OutputState = BTreeMap<Namespace, EvaluationState>;
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
                    imbl::OrdMap::default(),
                );
            }
        }
        Ok(analysis_state)
    }
    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::AnalysisState, Self::Error> {
        let mut new_analysis_state = analysis_state.clone();

        let namespace = Namespace::Module(node.clone());
        let constraint_graph = self.graph.get_constraint_graph(&namespace).unwrap();

        solve_namespace(&namespace, constraint_graph, &mut new_analysis_state)?;

        Ok(new_analysis_state)
    }
    fn get_input_state(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::InputState, Self::Error> {
        Ok(self
            .get_namespaces(&Namespace::Module(node.clone()))
            .unwrap()
            .into_iter()
            .map(|namespace| {
                let constraint_graph = self.graph.get_constraint_graph(namespace).unwrap();

                let mut program_evaluation: AbstractStateProxy<
                    '_,
                    _,
                    _,
                    ProgramEvaluation<EvaluationState>,
                > = AbstractStateProxy::with_default_proxy(&analysis_state.program_evaluation);
                let mut evaluator = ExpressionEvaluator::new(EvaluatorMode::Normal, namespace);

                (
                    namespace.clone(),
                    constraint_graph
                        .specification
                        .arguments
                        .iter()
                        .map(|(variable, expressions)| {
                            let ty = if let Ok(eval) =
                                evaluator.evaluate_expressions(&mut program_evaluation, expressions)
                            {
                                Deferred::known(Sourced::specified(eval.value))
                            } else {
                                Deferred::unknown(
                                    expressions
                                        .iter()
                                        .map(|expression| Arc::new(expression.clone()))
                                        .collect(),
                                )
                            };
                            (variable.clone(), ty)
                        })
                        .collect(),
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
            .unwrap()
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
            #raise = Inferred({})
            #return = Inferred(None)
        builtins[NameError@{4:6}]:
            #variables = {}
            #raise = Inferred({})
            #return = Inferred(None)
        builtins[int@{1:6}][__add__@{2:8}]:
            self@{builtins[int@{1:6}][__add__@{2:8}][2:16]} = Specified(Never)
            value@{builtins[int@{1:6}][__add__@{2:8}][2:22]} = Specified(@class(builtins[int@{1:6}]))
            #variables = {self: {builtins[int@{1:6}][__add__@{2:8}][2:16]}, value: {builtins[int@{1:6}][__add__@{2:8}][2:22]}}
            #raise = Inferred({})
            #return = Specified(@class(builtins[int@{1:6}]))
        builtins[int@{1:6}]:
            __add__@{builtins[int@{1:6}][2:8]} = Inferred(function(builtins[int@{1:6}][__add__@{2:8}]))
            #variables = {__add__: {builtins[int@{1:6}][2:8]}}
            #raise = Inferred({})
            #return = Inferred(None)
        "##};

        let module_loader = TestModuleLoader {
            modules: HashMap::from_iter([(
                BUILTINS_MODULE,
                TEST_BUILTINS.to_owned(),
            )]),
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
            #raise = Inferred({})
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
            #raise = Inferred({Exception(type=Any, origin=Unknown)}) ⊔ #deferred{(a) < (5)}
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[add_two@{1:4}]:
            a@{module[add_two@{1:4}][1:12]} = Specified(@class(builtins[int@{1:6}]))
            b@{module[add_two@{1:4}][1:20]} = Specified(@class(builtins[int@{1:6}]))
            #variables = {a: {module[add_two@{1:4}][1:12]}, b: {module[add_two@{1:4}][1:20]}}
            #raise = Inferred({})
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}]:
            b@{module[A@{1:6}][2:4]} = Inferred(5)
            #variables = {b: {module[A@{1:6}][2:4]}}
            #raise = Inferred({})
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}]:
            b@{module[A@{1:6}][2:4]} = Inferred(5)
            #variables = {b: {module[A@{1:6}][2:4]}}
            #raise = Inferred({})
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}]:
            foo@{module[A@{1:6}][2:8]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #variables = {foo: {module[A@{1:6}][2:8]}}
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}][foo@{2:8}]:
            #variables = {}
            #raise = Inferred({})
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}]:
            foo@{module[A@{1:6}][2:8]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #variables = {foo: {module[A@{1:6}][2:8]}}
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}][foo@{2:8}]:
            #variables = {}
            #raise = Inferred({})
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[foo@{1:4}]:
            #variables = {}
            #raise = Inferred({})
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[foo@{1:4}]:
            #variables = {}
            #raise = Inferred({})
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
