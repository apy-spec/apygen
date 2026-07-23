use crate::analysis::abstract_state::{AbstractState, AbstractStateProxy};
use crate::analysis::fmt::fmt_set;
use crate::analysis::lattice::Join;
use crate::analysis::{DummyAnalysisObserver, GraphAnalyser, analysis};
use crate::calls::Arguments;
use crate::constraint_graph::expressions::{
    BinaryOperator, Expression, ExpressionAnnotated, ExpressionAttribute, ExpressionBinary,
    ExpressionCall, ExpressionClass, ExpressionForwardVariable, ExpressionFunction,
    ExpressionSubscript, ExpressionUnary, ExpressionVariable, Identifier, ModuleName, Namespace,
    QualifiedName, VariableName,
};
use crate::constraint_graph::{
    Constraint, ConstraintGraph, ConstraintNode, Guard, ModuleDependentGraph, ModuleNode,
};
use crate::expressions::literal_class::method_resolution_order;
use crate::expressions::{PyEffects, PyTypeEval, gen_bool_value, type_literal};
use crate::identifiers::{Location, NamedQualifiedLocation};
use crate::inference::{
    BUILTINS_MODULE, Base, ClassType, DEPTH_LIMIT, Exception, ExceptionOrigin, FunctionType,
    LiteralClass, LiteralFunction, LiteralMethod, RaisedExceptions, Source, Sourced,
    StructuralDepth, StructuralWidth, Type, TypeInstance, TypeLiteral, WIDTH_LIMIT,
};
use crate::inference::{Deferred, DefinedVariables, NamespaceEvaluation, ProgramEvaluation};
use imbl::ordmap::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;
use std::fmt::{Debug, Display};
use std::sync::Arc;

pub use apygen_analysis as analysis;
pub use apygen_constraint_graph as constraint_graph;
pub use apygen_identifiers as identifiers;
pub use apygen_inference as inference;
pub use apygen_primitives as primitives;
pub use imbl;

pub mod calls;
pub mod expressions;

#[derive(Debug, Clone, PartialEq, Eq, Join)]
pub struct EvaluationState<E: Ord> {
    pub types: imbl::OrdMap<Arc<E>, Deferred<Sourced<Type>, E>>,
    pub return_value: Deferred<Sourced<Type>, E>,
    pub raised_exceptions: Deferred<Sourced<RaisedExceptions>, E>,
    pub defined_variables: DefinedVariables,
}

impl EvaluationState<Expression> {
    pub fn get_variable_type(
        &self,
        variable_name: &VariableName,
        locations: &imbl::OrdSet<(Arc<Namespace>, Location)>,
    ) -> Option<Deferred<Sourced<Type>, Expression>> {
        let mut ty = None;
        for (namespace, location) in locations {
            let variable =
                Expression::Variable(ExpressionVariable::new(NamedQualifiedLocation::new(
                    variable_name.clone(),
                    location.clone(),
                    namespace.clone(),
                )));
            ty = ty.join(&self.types.get(&variable).cloned());
        }
        ty
    }
}

impl<E: Ord> Default for EvaluationState<E> {
    fn default() -> Self {
        Self {
            types: imbl::OrdMap::new(),
            return_value: Deferred::unknown(imbl::OrdSet::new()),
            raised_exceptions: Deferred::unknown(imbl::OrdSet::new()),
            defined_variables: DefinedVariables::new(),
        }
    }
}

impl<E: Ord + Display> Display for EvaluationState<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("(evaluations: ")?;
        fmt_set(f, self.types.iter(), |f, (expression, eval)| {
            write!(f, "{}: {}", expression, eval)
        })?;
        write!(
            f,
            ", return: {}, raised: {}, defined_variables = {})",
            self.return_value, self.raised_exceptions, self.defined_variables
        )
    }
}

impl NamespaceEvaluation for EvaluationState<Expression> {
    type Expression = Expression;
    fn attributes(
        &self,
    ) -> impl Iterator<Item = (&VariableName, Deferred<Sourced<Type>, Self::Expression>)> {
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

    fn get_attribute(
        &self,
        name: &VariableName,
    ) -> Option<Deferred<Sourced<Type>, Self::Expression>> {
        self.defined_variables
            .names
            .get(name)
            .map(|locations| self.get_variable_type(name, locations).unwrap_or_default())
    }

    fn raised_exceptions(&self) -> &Deferred<Sourced<RaisedExceptions>, Self::Expression> {
        &self.raised_exceptions
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

impl<
    N: Clone + Ord,
    S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Clone,
> AbstractState for SolverState<N, S>
{
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

pub struct ExpressionEvaluator<'a> {
    pub namespace: &'a Namespace,
    pub constraint_graphs: &'a imbl::OrdMap<Arc<Namespace>, ConstraintGraph>,
    pub in_evaluation: &'a imbl::OrdSet<&'a Namespace>,
}

impl<'a> ExpressionEvaluator<'a> {
    pub fn new(
        namespace: &'a Namespace,
        constraint_graphs: &'a imbl::OrdMap<Arc<Namespace>, ConstraintGraph>,
        in_evaluation: &'a imbl::OrdSet<&'a Namespace>,
    ) -> Self {
        Self {
            namespace,
            constraint_graphs,
            in_evaluation,
        }
    }

    pub fn with_namespace(&self, namespace: &'a Namespace) -> Self {
        Self::new(namespace, self.constraint_graphs, self.in_evaluation)
    }

    pub fn simplify<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
    ) -> Option<()> {
        let mut types = abstract_state.get(&self.namespace)?.types.clone();

        loop {
            let mut changed = false;

            types = types
                .into_iter()
                .map(|(expression, evaluation)| {
                    if evaluation.expressions.is_empty() {
                        return (expression, evaluation);
                    }

                    let mut ty = Deferred::new(evaluation.value.clone(), imbl::OrdSet::default());

                    for expression in &evaluation.expressions {
                        match self.evaluate_expression(abstract_state, &expression) {
                            Some(type_eval) => {
                                ty.value = ty.value.join(&Sourced::inferred(type_eval.value));
                                changed = true;
                            }
                            None => {
                                ty.expressions.insert(expression.clone());
                            }
                        }
                    }

                    (expression, ty)
                })
                .collect();

            let evaluation_state = abstract_state
                .get_mut(&self.namespace)
                .expect("evaluation_state should exists");

            evaluation_state.types = types.clone();

            if !changed {
                break;
            }
        }

        Some(())
    }

    pub fn evaluate_expression_variable<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_variable: &ExpressionVariable,
    ) -> Option<PyTypeEval> {
        let evaluation_state =
            abstract_state.get(&expression_variable.named_qualified_location.namespace)?;

        let Some(ty) = evaluation_state
            .types
            .get(&Expression::Variable(expression_variable.clone()))
        else {
            return if evaluation_state
                .defined_variables
                .names
                .contains_key(&expression_variable.named_qualified_location.name)
            {
                Some(PyTypeEval::with_default_effects(Type::Never))
            } else {
                Some(PyTypeEval::new(
                    Type::Never,
                    PyEffects::new().with_exceptions(RaisedExceptions::raise(Exception::new(
                        Arc::new(Type::Instance(TypeInstance::from_qualified_name(
                            abstract_state,
                            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                            &Arc::new(Identifier::parse("NameError")),
                        )?)),
                        ExceptionOrigin::Specified, // TODO: fix origin
                    ))),
                ))
            };
        };

        Some(PyTypeEval::with_default_effects(
            ty.as_value()?.data.clone(),
        ))
    }

    pub fn evaluate_expression_forward_variable<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_forward_variable: &ExpressionForwardVariable,
    ) -> Option<PyTypeEval> {
        if let Some(program_evaluation) = abstract_state.get(self.namespace) {
            if let Some(ty) = program_evaluation.types.get(&Expression::ForwardVariable(
                expression_forward_variable.clone(),
            )) {
                return Some(PyTypeEval::with_default_effects(
                    ty.as_value()?.data.clone(),
                ));
            }
        }
        if let Some(parent_namespace) = self.namespace.parent() {
            return self
                .with_namespace(parent_namespace.as_ref())
                .evaluate_expression_forward_variable(abstract_state, expression_forward_variable);
        }

        Some(PyTypeEval::new(
            Type::Never,
            PyEffects::new().with_exceptions(RaisedExceptions::raise(Exception::new(
                Arc::new(Type::Instance(TypeInstance::from_qualified_name(
                    abstract_state,
                    &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                    &Arc::new(Identifier::parse("NameError")),
                )?)),
                ExceptionOrigin::Specified, // TODO: fix origin
            ))),
        ))
    }

    pub fn evaluate_expression_annotated<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_annotated: &ExpressionAnnotated,
    ) -> Option<PyTypeEval> {
        let annotation_eval =
            self.evaluate_expression(abstract_state, &expression_annotated.annotation)?;

        let Type::Literal(type_literal) = annotation_eval.value else {
            return None;
        };

        let base = match type_literal.as_ref() {
            TypeLiteral::Class(literal_class) => Base::Class(literal_class.clone()),
            TypeLiteral::TypeAlias(literal_type_alias) => {
                Base::TypeAlias(literal_type_alias.clone())
            }
            TypeLiteral::Generic(literal_generic) => Base::Generic(literal_generic.clone()),
            _ => return None,
        };

        Some(PyTypeEval::with_default_effects(Type::Instance(
            TypeInstance {
                base,
                arguments: imbl::Vector::new(),
            },
        )))
    }

    pub fn evaluate_expression_function<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_function: &ExpressionFunction,
    ) -> Option<PyTypeEval> {
        Some(PyTypeEval::with_default_effects(Type::new_literal(
            TypeLiteral::Function(LiteralFunction {
                value: Arc::new(FunctionType {
                    program_entity: expression_function.program_entity.clone(),
                    generics: Default::default(),
                    parameters: Default::default(),
                    is_async: expression_function.is_async,
                }),
            }),
        )))
    }

    pub fn evaluate_expression_class<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_class: &ExpressionClass,
    ) -> Option<PyTypeEval> {
        analyse_program_entity(
            abstract_state,
            self.constraint_graphs,
            &Namespace::NamedProgramEntity(expression_class.program_entity.clone()),
            self.in_evaluation.update(&self.namespace),
        )
        .unwrap();
        Some(PyTypeEval::with_default_effects(Type::new_literal(
            TypeLiteral::Class(LiteralClass {
                value: Arc::new(ClassType {
                    program_entity: expression_class.program_entity.clone(),
                    generics: Default::default(),
                    bases: Default::default(),
                    keyword_arguments: Default::default(),
                    is_abstract: false,
                }),
            }),
        )))
    }

    /// References: https://docs.python.org/3/howto/descriptor.html
    fn evaluate_attributes<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        value_ty: &Type,
        name: &VariableName,
        instance_arguments: Option<&imbl::Vector<Arc<Type>>>,
    ) -> Option<PyTypeEval> {
        match value_ty {
            Type::Instance(type_instance) => self.evaluate_attributes(
                abstract_state,
                &type_instance.base.as_type(),
                name,
                Some(&type_instance.arguments),
            ),
            Type::Union(type_union) => {
                let mut eval = PyTypeEval::never();
                for ty in &type_union.types {
                    eval = eval.join(&self.evaluate_attributes(abstract_state, ty, name, None)?);
                }
                Some(eval)
            }
            Type::Intersection(type_intersection) => {
                let mut eval = PyTypeEval::never();
                for ty in type_intersection {
                    eval = eval.join(&self.evaluate_attributes(abstract_state, ty, name, None)?);
                }
                Some(eval)
            }
            Type::Literal(type_literal) => match type_literal.as_ref() {
                TypeLiteral::Class(literal_class) => {
                    // TODO: add support for descriptors
                    for class in method_resolution_order(literal_class)? {
                        let class_namespace =
                            Namespace::NamedProgramEntity(class.value.program_entity.clone());

                        let evaluation_state =
                            if let Some(evaluation_state) = abstract_state.get(&class_namespace) {
                                evaluation_state
                            } else if self.in_evaluation.contains(self.namespace) {
                                return None;
                            } else {
                                analyse_program_entity(
                                    abstract_state,
                                    self.constraint_graphs,
                                    &class_namespace,
                                    self.in_evaluation.update(&self.namespace),
                                )
                                .unwrap()
                            };

                        let Some(locations) = evaluation_state.defined_variables.names.get(name)
                        else {
                            continue;
                        };

                        let mut eval = PyTypeEval::never();
                        for (program_entity, location) in locations {
                            let mut ty = evaluation_state
                                .types
                                .get(&Expression::Variable(ExpressionVariable::new(
                                    NamedQualifiedLocation::new(
                                        name.clone(),
                                        location.clone(),
                                        program_entity.clone(),
                                    ),
                                )))?
                                .as_value()?
                                .clone();

                            if let Type::Literal(type_literal) = &ty.data {
                                if let TypeLiteral::Function(literal_function) =
                                    type_literal.as_ref()
                                {
                                    if let Some(arguments) = instance_arguments {
                                        ty = Sourced::inferred(Type::new_literal(
                                            TypeLiteral::Method(LiteralMethod {
                                                class: class.value.clone(),
                                                function: literal_function.value.clone(),
                                                arguments: arguments.clone(),
                                            }),
                                        ));
                                    }
                                }
                            };

                            eval.value = eval.value.join(&ty.data);
                        }

                        return Some(eval);
                    }
                    None
                }
                _ => self.evaluate_attributes(
                    abstract_state,
                    &Type::Instance(type_literal.as_type_instance(abstract_state)?),
                    name,
                    None,
                ),
            },
            _ => None,
        }
    }

    pub fn evaluate_expression_attribute<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_attribute: &ExpressionAttribute,
    ) -> Option<PyTypeEval> {
        let mut effects = PyEffects::new();

        let value_ty = pytype_consume_or_return_option!(
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

    pub fn evaluate_expression_subscript<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_subscript: &ExpressionSubscript,
    ) -> Option<PyTypeEval> {
        let mut effects = PyEffects::new();

        let value_ty = pytype_consume_or_return_option!(
            effects,
            self.evaluate_expression(abstract_state, &expression_subscript.value)?
        );
        let get_item = self.evaluate_attributes(
            abstract_state,
            &value_ty,
            &Arc::new(Identifier::parse("__getitem__")),
            None,
        )?;
        let slice_ty = pytype_consume_or_return_option!(
            effects,
            self.evaluate_expression(abstract_state, &expression_subscript.slice)?
        );

        let ty = pytype_consume_or_return_option!(
            effects,
            self.evaluate_call(
                abstract_state,
                &get_item.value,
                Arguments::new().add_positional_argument(Arc::new(slice_ty))
            )?
        );

        Some(PyTypeEval::new(ty, effects))
    }

    pub fn evaluate_call<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        ty: &Type,
        arguments: Arguments,
    ) -> Option<PyTypeEval> {
        let Type::Literal(literal) = ty else {
            return None; // TODO: add support for unions, etc
        };

        match literal.as_ref() {
            TypeLiteral::Function(literal_function) => {
                let function_namespace =
                    Namespace::NamedProgramEntity(literal_function.value.program_entity.clone());

                let evaluation_state =
                    if let Some(evaluation_state) = abstract_state.get(&function_namespace) {
                        evaluation_state
                    } else if self.in_evaluation.contains(self.namespace) {
                        return None;
                    } else {
                        analyse_program_entity(
                            abstract_state,
                            self.constraint_graphs,
                            &function_namespace,
                            self.in_evaluation.update(self.namespace),
                        )
                        .unwrap()
                    };
                Some(PyTypeEval::new(
                    evaluation_state.return_value.as_value()?.data.clone(),
                    PyEffects::new().with_exceptions(
                        evaluation_state.raised_exceptions.as_value()?.data.clone(),
                    ),
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
            TypeLiteral::Class(literal_class) => Some(PyTypeEval::with_default_effects(
                Type::Instance(TypeInstance {
                    base: Base::Class(literal_class.clone()),
                    arguments: imbl::Vector::new(),
                }),
            )),
            _ => None, // TODO: add support for classes, etc
        }
    }

    pub fn evaluate_expression_call<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_call: &ExpressionCall,
    ) -> Option<PyTypeEval> {
        let mut effects = PyEffects::new();

        let ty = pytype_consume_or_return_option!(
            effects,
            self.evaluate_expression(abstract_state, &expression_call.target)?
        );

        let mut arguments = Arguments::new();

        for argument in &expression_call.positional_arguments {
            let argument_ty = pytype_consume_or_return_option!(
                effects,
                self.evaluate_expression(abstract_state, &argument)?
            );

            arguments.positional.push(Arc::new(argument_ty));
        }
        for keyword_argument in &expression_call.keyword_arguments {
            if let Some(name) = &keyword_argument.name {
                let keyword_argument_ty = pytype_consume_or_return_option!(
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

    pub fn evaluate_expression_unary<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_unary: &ExpressionUnary,
    ) -> Option<PyTypeEval> {
        let mut effects = PyEffects::new();

        let operand_ty = pytype_consume_or_return_option!(
            effects,
            self.evaluate_expression(abstract_state, &expression_unary.operand)?
        );

        let ty = match operand_ty {
            Type::Literal(type_literal) => {
                pytype_consume_or_return_option!(
                    effects,
                    type_literal::call_unary_op(type_literal.as_ref(), expression_unary.operator)
                )
            }
            Type::Never | Type::NoReturn => unreachable!("operand_ty should not be unreachable"),
            _ => return None,
        };

        Some(PyTypeEval::new(ty, effects))
    }

    pub fn evaluate_binary_operation<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        left_ty: &Type,
        operator: BinaryOperator,
        right_ty: &Type,
    ) -> Option<PyTypeEval> {
        match (left_ty, right_ty) {
            (Type::Literal(left), Type::Literal(right)) => Some(type_literal::call_binary_op(
                left.as_ref(),
                operator,
                right.as_ref(),
            )),
            (Type::Instance(_), _) => {
                let mut effects = PyEffects::new();

                let method = pytype_consume_or_return_option!(
                    effects,
                    self.evaluate_attributes(
                        abstract_state,
                        left_ty,
                        &Arc::new(Identifier::parse(&format!(
                            "__{}__",
                            operator.method_name()?
                        ))),
                        None
                    )?
                );

                let return_type = pytype_consume_or_return_option!(
                    effects,
                    self.evaluate_call(
                        abstract_state,
                        &method,
                        Arguments::new().add_positional_argument(Arc::new(right_ty.clone())),
                    )?
                );

                Some(PyTypeEval::new(return_type, effects))
            }
            (_, Type::Instance(_)) => {
                let mut effects = PyEffects::new();

                let method = pytype_consume_or_return_option!(
                    effects,
                    self.evaluate_attributes(
                        abstract_state,
                        right_ty,
                        &Arc::new(Identifier::parse(&format!(
                            "__r{}__",
                            operator.method_name()?
                        ))),
                        None
                    )?
                );

                let return_type = pytype_consume_or_return_option!(
                    effects,
                    self.evaluate_call(
                        abstract_state,
                        &method,
                        Arguments::new().add_positional_argument(Arc::new(left_ty.clone())),
                    )?
                );

                Some(PyTypeEval::new(return_type, effects))
            }
            (Type::Union(left_type_union), Type::Union(right_type_union)) => {
                let mut type_eval = PyTypeEval::never();
                for ty in &left_type_union.types {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        abstract_state,
                        ty,
                        operator,
                        right_ty,
                    )?);
                }
                for ty in &right_type_union.types {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        abstract_state,
                        left_ty,
                        operator,
                        ty,
                    )?);
                }
                Some(type_eval)
            }
            (Type::Union(left_type_union), _) => {
                let mut type_eval = PyTypeEval::never();
                for ty in &left_type_union.types {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        abstract_state,
                        ty,
                        operator,
                        right_ty,
                    )?);
                }
                Some(type_eval)
            }
            (_, Type::Union(right_type_union)) => {
                let mut type_eval = PyTypeEval::never();
                for ty in &right_type_union.types {
                    type_eval = type_eval.join(&self.evaluate_binary_operation(
                        abstract_state,
                        left_ty,
                        operator,
                        ty,
                    )?);
                }
                Some(type_eval)
            }
            (Type::Any, _) | (_, Type::Any) => Some(PyTypeEval::unknown()),
            (Type::Never, _) | (_, Type::Never) | (Type::NoReturn, _) | (_, Type::NoReturn) => {
                unreachable!()
            }
            _ => None, // TODO: add support for the rest
        }
    }

    pub fn evaluate_expression_binary<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression_binary: &ExpressionBinary,
    ) -> Option<PyTypeEval> {
        let mut effects = PyEffects::new();

        let left_ty = pytype_consume_or_return_option!(
            effects,
            self.evaluate_expression(abstract_state, &expression_binary.left)?
        );
        let right_ty = pytype_consume_or_return_option!(
            effects,
            self.evaluate_expression(abstract_state, &expression_binary.right)?
        );

        let ty = pytype_consume_or_return_option!(
            effects,
            self.evaluate_binary_operation(
                abstract_state,
                &left_ty,
                expression_binary.operator,
                &right_ty
            )?
        );

        Some(PyTypeEval::new(ty, effects))
    }

    pub fn evaluate_expression<
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expression: &Expression,
    ) -> Option<PyTypeEval> {
        if let Some(expression_eval) = abstract_state
            .get(self.namespace)
            .and_then(|state| state.types.get(expression))
        {
            return Some(PyTypeEval::with_default_effects(
                expression_eval.as_value()?.data.clone(),
            ));
        }

        match expression {
            Expression::Variable(expression_variable) => {
                self.evaluate_expression_variable(abstract_state, expression_variable)
            }
            Expression::ForwardVariable(expression_forward_variable) => self
                .evaluate_expression_forward_variable(abstract_state, expression_forward_variable),
            Expression::Annotated(expression_annotated) => {
                self.evaluate_expression_annotated(abstract_state, expression_annotated)
            }
            Expression::Override(_) => None,
            Expression::Function(expression_function) => {
                self.evaluate_expression_function(abstract_state, expression_function)
            }
            Expression::Class(expression_class) => {
                self.evaluate_expression_class(abstract_state, expression_class)
            }
            Expression::Import(_) => None,
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
            Expression::LiteralInteger(literal_integer) => Some(PyTypeEval::with_default_effects(
                Type::new_integer_literal(literal_integer.clone()),
            )),
            Expression::LiteralFloat(literal_float) => Some(PyTypeEval::with_default_effects(
                Type::new_float_literal(literal_float.clone()),
            )),
            Expression::LiteralComplex(literal_complex) => Some(PyTypeEval::with_default_effects(
                Type::new_complex_literal(literal_complex.clone()),
            )),
            Expression::LiteralString(literal_string) => Some(PyTypeEval::with_default_effects(
                Type::new_string_literal(literal_string.clone()),
            )),
            Expression::LiteralBytes(literal_bytes) => Some(PyTypeEval::with_default_effects(
                Type::new_bytes_literal(literal_bytes.clone()),
            )),
            Expression::LiteralBoolean(literal_boolean) => Some(PyTypeEval::with_default_effects(
                Type::new_boolean_literal(literal_boolean.clone()),
            )),
            Expression::LiteralNone => Some(PyTypeEval::with_default_effects(Type::new_literal(
                TypeLiteral::None,
            ))),
            Expression::LiteralEllipsis => Some(PyTypeEval::with_default_effects(
                Type::new_literal(TypeLiteral::Ellipsis),
            )),
        }
    }

    pub fn evaluate_expressions<
        'e,
        's,
        S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        expressions: impl IntoIterator<Item = &'e Expression>,
    ) -> Option<PyTypeEval> {
        let mut eval = PyTypeEval::never();

        for expression in expressions {
            eval = eval.join(&self.evaluate_expression(abstract_state, expression)?);
        }

        Some(eval)
    }
}

pub struct ConstraintSolver<
    's,
    S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>>,
> {
    pub namespace: &'s Namespace,
    pub constraint_graphs: &'s imbl::OrdMap<Arc<Namespace>, ConstraintGraph>,
    pub program_evaluation:
        &'s AbstractStateProxy<'s, S, ProgramEvaluation<EvaluationState<Expression>>>,
    pub in_evaluation: imbl::OrdSet<&'s Namespace>,
}

impl<'s, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>>>
    ConstraintSolver<'s, S>
{
    pub fn new(
        namespace: &'s Namespace,
        constraint_graphs: &'s imbl::OrdMap<Arc<Namespace>, ConstraintGraph>,
        program_evaluation: &'s AbstractStateProxy<
            's,
            S,
            ProgramEvaluation<EvaluationState<Expression>>,
        >,
        in_evaluation: imbl::OrdSet<&'s Namespace>,
    ) -> Self {
        Self {
            namespace,
            constraint_graphs,
            program_evaluation,
            in_evaluation,
        }
    }

    pub fn constraint_graph(&self) -> Option<&ConstraintGraph> {
        self.constraint_graphs.get(self.namespace)
    }

    pub fn evaluator(&self) -> ExpressionEvaluator<'_> {
        ExpressionEvaluator::new(self.namespace, self.constraint_graphs, &self.in_evaluation)
    }
}

impl<'s, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq>
    GraphAnalyser for ConstraintSolver<'s, S>
{
    type Node = ConstraintNode;
    type AbstractState = AbstractStateProxy<'s, S, ProgramEvaluation<EvaluationState<Expression>>>;
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
            .constraint_graph()
            .unwrap()
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
        let mut program_evaluation =
            analysis_state.get_clone_or_else(node, || self.program_evaluation.clone());

        match &node {
            ConstraintNode::Entry => {
                let specification = &self.constraint_graph().unwrap().specification;

                let arguments: BTreeMap<_, _> = specification
                    .arguments
                    .iter()
                    .map(|(variable, expressions)| {
                        let ty = if let Some(eval) = self
                            .evaluator()
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
                        if let Some(eval) = self
                            .evaluator()
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

                let return_ty = if let Some(eval) = self
                    .evaluator()
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

                    evaluation_state
                        .types
                        .insert(Arc::new(Expression::Variable(variable.clone())), ty);
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
            ConstraintNode::Constraint { .. } => {
                if let Some(constraints) = self.constraint_graph().unwrap().nodes.get(node) {
                    for constraint in constraints {
                        match constraint {
                            Constraint::Type(type_constraint) => {
                                let (ty, raised_exceptions) =
                                    match self.evaluator().evaluate_expression(
                                        &mut program_evaluation,
                                        &type_constraint.left,
                                    ) {
                                        Some(type_eval) => (
                                            Deferred::known(Sourced::inferred(type_eval.value)),
                                            Deferred::known(Sourced::inferred(
                                                type_eval.effects.exceptions,
                                            )),
                                        ),
                                        None => (
                                            Deferred::unknown(imbl::OrdSet::unit(
                                                type_constraint.left.clone(),
                                            )),
                                            Deferred::unknown(imbl::OrdSet::unit(
                                                type_constraint.left.clone(),
                                            )),
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
                            }
                            Constraint::Return(return_constraint) => {
                                let (ty, raised_exceptions) =
                                    match self.evaluator().evaluate_expression(
                                        &mut program_evaluation,
                                        &return_constraint.expression,
                                    ) {
                                        Some(type_eval) => (
                                            Deferred::known(Sourced::inferred(type_eval.value)),
                                            Deferred::known(Sourced::inferred(
                                                type_eval.effects.exceptions,
                                            )),
                                        ),
                                        None => (
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
            .constraint_graph()
            .unwrap()
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
                        .evaluator()
                        .evaluate_expression(&mut new_abstract_state, expression);

                    if let Some(type_eval) = eval {
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
                        .evaluator()
                        .evaluate_expression(&mut new_abstract_state, expression);

                    if let Some(type_eval) = eval {
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
                        .evaluator()
                        .evaluate_expression(&mut new_abstract_state, expression);

                    if let Some(type_eval) = eval {
                        if is_type_unreachable!(type_eval.value) {
                            continue;
                        }
                    }
                    should_ignore = false;
                }
                Guard::Raise { expression, .. } => {
                    let eval = self
                        .evaluator()
                        .evaluate_expression(&mut new_abstract_state, expression);

                    let evaluation_state =
                        new_abstract_state.get_or_insert_default(self.namespace.clone());

                    if let Some(type_eval) = eval {
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
        assert!(std::ptr::eq(
            left.abstract_state,
            self.program_evaluation.abstract_state
        ));
        assert!(std::ptr::eq(
            right.abstract_state,
            self.program_evaluation.abstract_state
        ));

        let mut new_abstract_state = AbstractStateProxy::new(
            self.program_evaluation.abstract_state,
            left.proxy.join(&right.proxy),
        );

        self.evaluator().simplify(&mut new_abstract_state);

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
                                for ty in type_union.types {
                                    new_ty = new_ty.join(&if let Type::Literal(type_literal) = &ty {
                                        type_literal
                                            .as_type_instance(&new_abstract_state)
                                            .map(|type_instance| {
                                                Type::Instance(type_instance)
                                            })
                                            .expect("should be able to convert type literal to type instance")
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

pub fn analyse_program_entity<
    'e,
    's: 'e,
    S: AbstractState<Key = Namespace, AbstractValue = EvaluationState<Expression>> + Eq,
>(
    abstract_state: &'e mut AbstractStateProxy<
        's,
        S,
        ProgramEvaluation<EvaluationState<Expression>>,
    >,
    constraint_graphs: &imbl::OrdMap<Arc<Namespace>, ConstraintGraph>,
    namespace: &'e Namespace,
    in_evaluation: imbl::OrdSet<&'e Namespace>,
) -> Result<&'e mut EvaluationState<Expression>, Infallible> {
    let solver_state = analysis(
        &ConstraintSolver::new(namespace, constraint_graphs, abstract_state, in_evaluation),
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
        abstract_state.proxy = new_abstract_state.proxy;
    }

    Ok(abstract_state.insert(namespace.clone(), evaluation_state))
}

pub struct ModuleConstraintSolver<'a> {
    pub graph: &'a ModuleDependentGraph,
}

impl<'a> ModuleConstraintSolver<'a> {
    pub fn new(graph: &'a ModuleDependentGraph) -> Self {
        Self { graph }
    }
}

impl GraphAnalyser for ModuleConstraintSolver<'_> {
    type Node = ModuleNode;
    type AbstractState = ProgramEvaluation<EvaluationState<Expression>>;
    type AnalysisState = SolverState<Self::Node, Self::AbstractState>;
    type Error = Infallible;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error> {
        Ok(std::iter::once(ModuleNode::Entry))
    }

    fn next_nodes(
        &self,
        node: &Self::Node,
    ) -> Result<impl Iterator<Item = &Self::Node>, Self::Error> {
        Ok(self
            .graph
            .dependents
            .get(node)
            .map(|nodes| nodes.iter())
            .into_iter()
            .flatten())
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        Ok(SolverState::default())
    }

    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::AbstractState, Self::Error> {
        let mut new_analysis_state = analysis_state.get_clone_or_default(node);

        let ModuleNode::Module(module_name) = &node else {
            return Ok(new_analysis_state);
        };

        let program_entity_constraints = self.graph.nodes.get(&node).unwrap();

        let namespace = Namespace::Module(module_name.clone());

        let mut proxy = AbstractStateProxy::with_default_proxy(&new_analysis_state);

        analyse_program_entity(
            &mut proxy,
            program_entity_constraints,
            &namespace,
            imbl::OrdSet::new(),
        )?;

        new_analysis_state.extend(proxy.proxy.states);

        for other_namespace in program_entity_constraints.keys() {
            if **other_namespace != namespace {
                let mut proxy = AbstractStateProxy::with_default_proxy(&new_analysis_state);

                analyse_program_entity(
                    &mut proxy,
                    program_entity_constraints,
                    other_namespace,
                    imbl::OrdSet::new(),
                )?;

                new_analysis_state.extend(proxy.proxy.states);
            }
        }

        Ok(new_analysis_state)
    }

    fn update_abstract_state(
        &self,
        _analysis_state: &Self::AnalysisState,
        _from: &Self::Node,
        _to: &Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error> {
        Ok(Some(abstract_state.clone()))
    }

    fn get_abstract_state<'a>(
        &self,
        analysis_state: &'a Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Option<&'a Self::AbstractState>, Self::Error> {
        Ok(analysis_state.get(node))
    }

    fn set_abstract_state(
        &self,
        analysis_state: &mut Self::AnalysisState,
        node: &Self::Node,
        abstract_state: Self::AbstractState,
    ) -> Result<(), Self::Error> {
        analysis_state.insert(node.clone(), abstract_state);
        Ok(())
    }

    fn merge(
        &self,
        _analysis_state: &Self::AnalysisState,
        _node: &Self::Node,
        left: &Self::AbstractState,
        right: &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error> {
        Ok(left.join(right))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inference::BUILTINS_MODULE;
    use apy::v1::QualifiedName;
    use apygen_analysis::analysis;
    use apygen_analysis::log::LogAnalysisObserver;
    use apygen_constraint_builder::{ModuleLoader, analyse_program};
    use indoc::indoc;
    use rstest::rstest;
    use std::collections::HashMap;

    fn init_logger() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    pub struct TestModuleLoader {
        pub modules: HashMap<ModuleName, String>,
    }

    impl ModuleLoader for TestModuleLoader {
        type Error = Infallible;
        fn load(&self, module_name: &ModuleName) -> Result<String, Self::Error> {
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
            a@{module[4:4]} = Inferred(Union[@class(builtins[int@{1:6}]), 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20])
            b@{module[6:0]} = Inferred(Union[@class(builtins[int@{1:6}]), 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20])
            #raise = Inferred({Exception(type=Any, origin=Unknown)}) ⊔ #deferred{(a@{module[3:6]}) < (5)}
            #return = Inferred(None)
        "##},  // TODO: fix this when operations are implemented
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[add_two@{1:4}]:
            a@{module[add_two@{1:4}][1:12]} = Specified(@class(builtins[int@{1:6}]))
            b@{module[add_two@{1:4}][1:20]} = Specified(@class(builtins[int@{1:6}]))
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}]:
            b@{module[A@{1:6}][2:4]} = Inferred(5)
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}]:
            b@{module[A@{1:6}][2:4]} = Inferred(5)
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}]:
            foo@{module[A@{1:6}][2:8]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}][foo@{2:8}]:
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}]:
            foo@{module[A@{1:6}][2:8]} = Inferred(function(module[A@{1:6}][foo@{2:8}]))
            #raise = Inferred({})
            #return = Inferred(None)
        module[A@{1:6}][foo@{2:8}]:
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
            #raise = Inferred({Exception(type=@class(builtins[NameError@{4:6}]), origin=Specified)})
            #return = Inferred(Never)
        module[foo@{1:4}]:
            #raise = Inferred({Exception(type=@class(builtins[NameError@{4:6}]), origin=Specified)})
            #return = Inferred(Never)
        "##},
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
            #raise = Inferred({})
            #return = Inferred(None)
        module[foo@{1:4}]:
            #raise = Inferred({})
            #return = Inferred(5)
        "##},
    )]
    fn test_constraints_solving(#[case] source: &str, #[case] expected_types: &str) {
        init_logger();

        let module_name = Arc::new(QualifiedName::parse("module"));
        let module_loader = TestModuleLoader {
            modules: HashMap::from_iter([
                (module_name.clone(), source.to_string()),
                (
                    Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                    TEST_BUILTINS.to_owned(),
                ),
            ]),
        };

        let dependent_graph = analyse_program(&module_loader, std::iter::once(module_name.clone()));

        let solver = ModuleConstraintSolver::new(&dependent_graph);

        let program_evaluation = analysis(&solver, &mut LogAnalysisObserver::default())
            .expect("analysis should work")
            .abstract_states[&ModuleNode::Exit]
            .clone();

        let mut actual_types = String::new();
        for (qualified_location, abstract_state) in &program_evaluation.states {
            if *qualified_location.module_name() != module_name {
                continue;
            }
            actual_types.push_str(&format!("{}:\n", qualified_location));
            for (variable_name, variable_locations) in &abstract_state.defined_variables.names {
                for (variable_namespace, variable_location) in variable_locations {
                    let expression_variable = ExpressionVariable::new(NamedQualifiedLocation::new(
                        variable_name.clone(),
                        variable_location.clone(),
                        variable_namespace.clone(),
                    ));
                    let variable_type = abstract_state
                        .types
                        .get(&Expression::Variable(expression_variable.clone()))
                        .cloned()
                        .unwrap_or_default();
                    actual_types.push_str(&format!(
                        "    {} = {}\n",
                        expression_variable, variable_type
                    ));
                }
            }
            actual_types.push_str(&format!(
                "    #raise = {}\n",
                abstract_state.raised_exceptions
            ));
            actual_types.push_str(&format!("    #return = {}\n", abstract_state.return_value));
        }

        assert_eq!(expected_types, actual_types, "{actual_types}");
    }
}
