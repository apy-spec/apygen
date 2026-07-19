use crate::abstract_environment::{
    BUILTINS_MODULE, Base, ClassType, DEPTH_LIMIT, Exception, ExceptionOrigin, FunctionType,
    LiteralClass, LiteralFunction, LiteralMethod, RaisedExceptions, StructuralDepth,
    StructuralWidth, TYPES_MODULE, Type, TypeInstance, TypeLiteral, TypeUnion, WIDTH_LIMIT,
};
use crate::constraints::{
    BinaryOperator, Constraint, ConstraintNode, DependentGraph, Expression, ExpressionAnnotated,
    ExpressionAttribute, ExpressionBinary, ExpressionCall, ExpressionClass, ExpressionFunction,
    ExpressionSubscript, ExpressionUnary, ExpressionVariable, Guard, Location, ModuleName,
    ModuleNode, ProgramEntityConstraints, QualifiedLocation, VariableName,
};
use crate::genkill::calls::Arguments;
use crate::genkill::expressions::literal_class::method_resolution_order;
use crate::genkill::expressions::{PyEffects, PyTypeEval, gen_bool_value, type_literal};
use crate::{is_type_unreachable, pytype_consume_or_return_option};
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::abstract_state::{AbstractState, AbstractStateProxy};
use apygen_analysis::fmt::{fmt_display_set, fmt_set};
use apygen_analysis::lattice::Join;
use apygen_analysis::{DummyAnalysisObserver, GraphAnalyser, analysis};
use imbl::ordmap::Entry;
use std::convert::Infallible;
use std::fmt::{Debug, Display};
use std::sync::Arc;

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct DefinedVariables {
    pub names: imbl::OrdMap<VariableName, imbl::OrdSet<(QualifiedLocation, Location)>>,
}

impl DefinedVariables {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Display for DefinedVariables {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_set(f, self.names.iter(), |f, (name, locations)| {
            write!(f, "{}: ", name)?;
            fmt_set(f, locations.iter(), |f, (program_entity, location)| {
                write!(f, "{}[{}]", program_entity, location)
            })
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Join)]
pub struct Deferred<T> {
    value: T,
    expressions: imbl::OrdSet<Arc<Expression>>,
}

impl<T> Deferred<T> {
    pub fn new(value: T, expressions: imbl::OrdSet<Arc<Expression>>) -> Self {
        Self { value, expressions }
    }

    pub fn known(value: T) -> Self {
        Self::new(value, imbl::OrdSet::default())
    }

    pub fn unknown(expressions: imbl::OrdSet<Arc<Expression>>) -> Self
    where
        T: Default,
    {
        Self::new(T::default(), expressions)
    }

    pub fn as_value(&self) -> Option<&T> {
        if self.expressions.is_empty() {
            Some(&self.value)
        } else {
            None
        }
    }

    pub fn to_value(self) -> Option<T> {
        if self.expressions.is_empty() {
            Some(self.value)
        } else {
            None
        }
    }
}

impl<T: Display> Display for Deferred<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.expressions.is_empty() {
            write!(f, "{}", self.value)
        } else {
            write!(f, "{} ⊔ #deferred", self.value)?;
            fmt_display_set(f, self.expressions.iter())
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, Join)]
pub struct EvaluationState {
    pub types: imbl::OrdMap<Arc<Expression>, Deferred<Type>>,
    pub return_value: Deferred<Type>,
    pub raised_exceptions: Deferred<RaisedExceptions>,
    pub defined_variables: DefinedVariables,
}

impl Display for EvaluationState {
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

impl EvaluationState {
    pub fn variables(&self) -> impl Iterator<Item = (ExpressionVariable, Deferred<Type>)> {
        self.defined_variables
            .names
            .iter()
            .flat_map(|(variable, locations)| {
                locations.iter().map(|(program_entity, location)| {
                    let expression_variable = ExpressionVariable::new(
                        variable.clone(),
                        location.clone(),
                        program_entity.clone(),
                    );

                    (
                        expression_variable.clone(),
                        self.types
                            .get(&Expression::Variable(expression_variable))
                            .cloned()
                            .unwrap_or_default(),
                    )
                })
            })
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
    S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Clone,
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
    pub qualified_location: &'a QualifiedLocation,
    pub program_entity_constraints: &'a imbl::OrdMap<QualifiedLocation, ProgramEntityConstraints>,
}

impl<'a> ExpressionEvaluator<'a> {
    pub fn new(
        qualified_location: &'a QualifiedLocation,
        program_entity_constraints: &'a imbl::OrdMap<QualifiedLocation, ProgramEntityConstraints>,
    ) -> Self {
        Self {
            qualified_location,
            program_entity_constraints,
        }
    }

    pub fn with_qualified_location(&self, qualified_location: &'a QualifiedLocation) -> Self {
        Self::new(qualified_location, self.program_entity_constraints)
    }

    pub fn get_variable_type(
        abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
        module_name: &ModuleName,
        name: &VariableName,
    ) -> Option<TypeInstance> {
        let evaluation_state = abstract_state.get(&QualifiedLocation::new(
            module_name.clone(),
            imbl::Vector::new(),
        ))?;

        let locations = evaluation_state.defined_variables.names.get(name)?;

        let (program_entity, location) = locations.get_min()?;

        let ty = evaluation_state
            .types
            .get(&Expression::Variable(ExpressionVariable::new(
                name.clone(),
                location.clone(),
                program_entity.clone(),
            )))?
            .as_value()?;

        let Type::Literal(type_literal) = ty else {
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

        Some(TypeInstance {
            base,
            arguments: imbl::Vector::new(),
        })
    }

    pub fn type_instance(
        abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
        ty: &TypeLiteral,
    ) -> Option<TypeInstance> {
        match ty {
            TypeLiteral::Integer(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("int")),
            ),
            TypeLiteral::Boolean(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("bool")),
            ),
            TypeLiteral::Float(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("float")),
            ),
            TypeLiteral::Complex(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("complex")),
            ),
            TypeLiteral::String(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("str")),
            ),
            TypeLiteral::Bytes(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("bytes")),
            ),
            TypeLiteral::None => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(TYPES_MODULE)),
                &Arc::new(Identifier::parse("NoneType")),
            ),
            TypeLiteral::Ellipsis => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(TYPES_MODULE)),
                &Arc::new(Identifier::parse("EllipsisType")),
            ),
            TypeLiteral::List(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("list")),
            ),
            TypeLiteral::Tuple(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("tuple")),
            ),
            TypeLiteral::Dict(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("dict")),
            ),
            TypeLiteral::Function(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(TYPES_MODULE)),
                &Arc::new(Identifier::parse("FunctionType")),
            ),
            TypeLiteral::OverloadedFunction(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(TYPES_MODULE)),
                &Arc::new(Identifier::parse("FunctionType")),
            ),
            TypeLiteral::Method(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(TYPES_MODULE)),
                &Arc::new(Identifier::parse("MethodType")),
            ),
            TypeLiteral::Class(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                &Arc::new(Identifier::parse("type")),
            ),
            TypeLiteral::TypeAlias(_) => None,
            TypeLiteral::Generic(_) => None,
            TypeLiteral::ImportedModule(_) => Self::get_variable_type(
                abstract_state,
                &Arc::new(QualifiedName::parse(TYPES_MODULE)),
                &Arc::new(Identifier::parse("ModuleType")),
            ),
        }
    }

    pub fn simplify<
        's,
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
    ) -> Option<()> {
        let mut types = abstract_state.get(&self.qualified_location)?.types.clone();

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
                                ty.value = ty.value.join(&type_eval.value);
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
                .get_mut(&self.qualified_location)
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
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
        expression_variable: &ExpressionVariable,
    ) -> Option<PyTypeEval> {
        let evaluation_state = abstract_state.get(&expression_variable.program_entity)?;

        let Some(ty) = evaluation_state
            .types
            .get(&Expression::Variable(expression_variable.clone()))
        else {
            return if evaluation_state
                .defined_variables
                .names
                .contains_key(&expression_variable.name)
            {
                Some(PyTypeEval::with_default_effects(Type::Never))
            } else {
                Some(PyTypeEval::new(
                    Type::Never,
                    PyEffects::new().with_exceptions(RaisedExceptions::raise(Exception::new(
                        Arc::new(Type::Instance(Self::get_variable_type(
                            abstract_state,
                            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                            &Arc::new(Identifier::parse("NameError")),
                        )?)),
                        ExceptionOrigin::Specified, // TODO: fix origin
                    ))),
                ))
            };
        };

        Some(PyTypeEval::with_default_effects(ty.as_value()?.clone()))
    }

    pub fn evaluate_expression_annotated<
        's,
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
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
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
        expression_function: &ExpressionFunction,
    ) -> Option<PyTypeEval> {
        if abstract_state.contains(&self.qualified_location) {
            analyse_program_entity(
                abstract_state,
                self.program_entity_constraints,
                &expression_function.identifier.qualified_location,
            )
            .unwrap();
        }
        Some(PyTypeEval::with_default_effects(Type::new_literal(
            TypeLiteral::Function(LiteralFunction {
                value: Arc::new(FunctionType {
                    identifier: expression_function.identifier.clone(),
                    generics: Default::default(),
                    parameters: Default::default(),
                    is_async: expression_function.is_async,
                }),
            }),
        )))
    }

    pub fn evaluate_expression_class<
        's,
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
        expression_class: &ExpressionClass,
    ) -> Option<PyTypeEval> {
        analyse_program_entity(
            abstract_state,
            self.program_entity_constraints,
            &expression_class.identifier.qualified_location,
        )
        .unwrap();
        Some(PyTypeEval::with_default_effects(Type::new_literal(
            TypeLiteral::Class(LiteralClass {
                value: Arc::new(ClassType {
                    identifier: expression_class.identifier.clone(),
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
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
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
                for ty in type_union.types() {
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
                        let evaluation_state = if let Some(evaluation_state) =
                            abstract_state.get(&class.value.identifier.qualified_location)
                        {
                            evaluation_state
                        } else {
                            analyse_program_entity(
                                abstract_state,
                                self.program_entity_constraints,
                                &class.value.identifier.qualified_location,
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
                                    name.clone(),
                                    location.clone(),
                                    program_entity.clone(),
                                )))?
                                .as_value()?
                                .clone();

                            if let Type::Literal(type_literal) = &ty {
                                if let TypeLiteral::Function(literal_function) =
                                    type_literal.as_ref()
                                {
                                    if let Some(arguments) = instance_arguments {
                                        ty =
                                            Type::new_literal(TypeLiteral::Method(LiteralMethod {
                                                class: class.value.clone(),
                                                function: literal_function.value.clone(),
                                                arguments: arguments.clone(),
                                            }));
                                    }
                                }
                            };

                            eval.value = eval.value.join(&ty);
                        }

                        return Some(eval);
                    }
                    None
                }
                _ => self.evaluate_attributes(
                    abstract_state,
                    &Type::Instance(Self::type_instance(abstract_state, type_literal)?),
                    name,
                    None,
                ),
            },
            _ => None,
        }
    }

    pub fn evaluate_expression_attribute<
        's,
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
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
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
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
                &Arguments::new().add_positional_argument(Arc::new(slice_ty))
            )?
        );

        Some(PyTypeEval::new(ty, effects))
    }

    pub fn evaluate_call<
        's,
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
        ty: &Type,
        arguments: &Arguments,
    ) -> Option<PyTypeEval> {
        let Type::Literal(literal) = ty else {
            return None; // TODO: add support for unions, etc
        };

        match literal.as_ref() {
            TypeLiteral::Function(literal_function) => {
                let evaluation_state = if let Some(evaluation_state) =
                    abstract_state.get(&literal_function.value.identifier.qualified_location)
                {
                    evaluation_state
                } else {
                    analyse_program_entity(
                        abstract_state,
                        self.program_entity_constraints,
                        &literal_function.value.identifier.qualified_location,
                    )
                    .unwrap()
                };

                Some(PyTypeEval::new(
                    evaluation_state.return_value.as_value()?.clone(),
                    PyEffects::new()
                        .with_exceptions(evaluation_state.raised_exceptions.as_value()?.clone()),
                ))
            }
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
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
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

        self.evaluate_call(abstract_state, &ty, &arguments)
    }

    pub fn evaluate_expression_unary<
        's,
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
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
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
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
                Some(type_eval)
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
                Some(type_eval)
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
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
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
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
        expression: &Expression,
    ) -> Option<PyTypeEval> {
        if let Some(expression_eval) = abstract_state
            .get(self.qualified_location)
            .and_then(|state| state.types.get(expression))
        {
            return Some(PyTypeEval::with_default_effects(
                expression_eval.as_value()?.clone(),
            ));
        }

        match expression {
            Expression::Variable(expression_variable) => {
                self.evaluate_expression_variable(abstract_state, expression_variable)
            }
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
        S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
    >(
        &self,
        abstract_state: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
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
    S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
> {
    pub qualified_location: &'s QualifiedLocation,
    pub program_entity_constraints: &'s imbl::OrdMap<QualifiedLocation, ProgramEntityConstraints>,
    pub program_evaluation: &'s AbstractStateProxy<'s, S, ProgramEvaluation>,
}

impl<'s, S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>>
    ConstraintSolver<'s, S>
{
    pub fn new(
        qualified_location: &'s QualifiedLocation,
        program_entity_constraints: &'s imbl::OrdMap<QualifiedLocation, ProgramEntityConstraints>,
        program_evaluation: &'s AbstractStateProxy<'s, S, ProgramEvaluation>,
    ) -> Self {
        Self {
            qualified_location,
            program_entity_constraints,
            program_evaluation,
        }
    }

    pub fn constraints(&self) -> Option<&ProgramEntityConstraints> {
        self.program_entity_constraints
            .get(&self.qualified_location)
    }

    pub fn evaluator(&self) -> ExpressionEvaluator<'_> {
        ExpressionEvaluator::new(self.qualified_location, self.program_entity_constraints)
    }

    pub fn evaluate_constraint(
        &self,
        program_evaluation: &mut AbstractStateProxy<'s, S, ProgramEvaluation>,
        constraint: &Constraint,
    ) where
        S: Eq,
    {
        match constraint {
            Constraint::Type(type_constraint) => {
                let (ty, raised_exceptions) = match self
                    .evaluator()
                    .evaluate_expression(program_evaluation, &type_constraint.left)
                {
                    Some(type_eval) => (
                        Deferred::known(type_eval.value),
                        Deferred::known(type_eval.effects.exceptions),
                    ),
                    None => (
                        Deferred::unknown(imbl::OrdSet::unit(type_constraint.left.clone())),
                        Deferred::unknown(imbl::OrdSet::unit(type_constraint.left.clone())),
                    ),
                };

                let evaluation_state =
                    program_evaluation.get_or_insert_default(self.qualified_location.clone());

                evaluation_state
                    .types
                    .entry(type_constraint.right.clone())
                    .and_modify(|previous_eval| *previous_eval = previous_eval.join(&ty))
                    .or_insert(ty);
                evaluation_state.raised_exceptions =
                    evaluation_state.raised_exceptions.join(&raised_exceptions);
            }
            Constraint::Return(return_constraint) => {
                let (ty, raised_exceptions) = match self
                    .evaluator()
                    .evaluate_expression(program_evaluation, &return_constraint.expression)
                {
                    Some(type_eval) => (
                        Deferred::known(type_eval.value),
                        Deferred::known(type_eval.effects.exceptions),
                    ),
                    None => (
                        Deferred::unknown(imbl::OrdSet::unit(return_constraint.expression.clone())),
                        Deferred::unknown(imbl::OrdSet::unit(return_constraint.expression.clone())),
                    ),
                };

                let evaluation_state =
                    program_evaluation.get_or_insert_default(self.qualified_location.clone());

                evaluation_state.return_value = ty;
                evaluation_state.raised_exceptions = raised_exceptions.join(&raised_exceptions);
            }
            Constraint::DefinedVariable(expression) => {
                let evaluation_state =
                    program_evaluation.get_or_insert_default(self.qualified_location.clone());

                evaluation_state.defined_variables.names.insert(
                    expression.name.clone(),
                    imbl::OrdSet::unit((
                        expression.program_entity.clone(),
                        expression.location.clone(),
                    )),
                );
            }
            Constraint::Multiple(constraints) => {
                for constraint in constraints {
                    self.evaluate_constraint(program_evaluation, constraint);
                }
            }
        }
    }
}

impl<'s, S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq>
    GraphAnalyser for ConstraintSolver<'s, S>
{
    type Node = ConstraintNode;
    type AbstractState = AbstractStateProxy<'s, S, ProgramEvaluation>;
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
            .constraints()
            .unwrap()
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
        let mut program_evaluation =
            analysis_state.get_clone_or_else(node, || self.program_evaluation.clone());

        match &node {
            ConstraintNode::Entry => {
                for (variable, expressions) in
                    self.constraints().unwrap().specification.arguments.as_ref()
                {
                    let mut ty: Deferred<Type> = Deferred::default();
                    let mut raised_exceptions: Deferred<RaisedExceptions> = Deferred::default();
                    for expression in expressions {
                        match self
                            .evaluator()
                            .evaluate_expression(&mut program_evaluation, expression)
                        {
                            Some(type_eval) => {
                                ty.value = ty.value.join(&type_eval.value);
                                raised_exceptions
                                    .value
                                    .exceptions
                                    .extend(type_eval.effects.exceptions.exceptions);
                            }
                            None => {
                                ty.expressions.insert(Arc::new(expression.clone()));
                                raised_exceptions
                                    .expressions
                                    .insert(Arc::new(expression.clone()));
                            }
                        }
                    }

                    let evaluation_state =
                        program_evaluation.get_or_insert_default(self.qualified_location.clone());

                    evaluation_state.defined_variables.names.insert(
                        variable.name.clone(),
                        imbl::OrdSet::unit((
                            variable.program_entity.clone(),
                            variable.location.clone(),
                        )),
                    );

                    evaluation_state
                        .types
                        .insert(Arc::new(Expression::Variable(variable.clone())), ty);
                    evaluation_state.raised_exceptions =
                        evaluation_state.raised_exceptions.join(&raised_exceptions);
                }
            }
            ConstraintNode::Constraint { .. } => {
                if let Some(constraint) =
                    self.constraints().unwrap().constraint_graph.nodes.get(node)
                {
                    self.evaluate_constraint(&mut program_evaluation, constraint);
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
            .constraints()
            .unwrap()
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
                        new_abstract_state.get_or_insert_default(self.qualified_location.clone());

                    if let Some(type_eval) = eval {
                        evaluation_state
                            .raised_exceptions
                            .value
                            .exceptions
                            .extend(type_eval.effects.exceptions.exceptions)
                    }
                    should_ignore = false;
                }
            }
        }

        if matches!(to, ConstraintNode::Exit) && self.qualified_location.locations.is_empty() {
            for other_qualified_location in self.program_entity_constraints.keys() {
                if self.qualified_location != other_qualified_location {
                    analyse_program_entity(
                        &mut new_abstract_state,
                        self.program_entity_constraints,
                        other_qualified_location,
                    )
                    .unwrap();
                }
            }
        }

        if should_ignore {
            Ok(None)
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

        if let Some(evaluation_state) = new_abstract_state.get(&self.qualified_location) {
            let new_evaluations = evaluation_state
                .types
                .clone()
                .into_iter()
                .map(|(expression, mut eval)| {
                    while eval.value.width() > WIDTH_LIMIT {
                        eval.value = match eval.value {
                            Type::Union(type_union) => {
                                let mut new_type_union = TypeUnion::new();
                                for ty in type_union.types() {
                                    new_type_union.add_type(
                                        if let Type::Literal(type_literal) = ty.as_ref() {
                                            Arc::new(
                                                ExpressionEvaluator::type_instance(
                                                    &new_abstract_state,
                                                    type_literal,
                                                )
                                                .map(|type_instance| Type::Instance(type_instance))
                                                .unwrap_or(Type::Any),
                                            )
                                        } else {
                                            ty.clone()
                                        },
                                    );
                                }
                                new_type_union.simplify().as_ref().clone()
                            }
                            _ => Type::Any,
                        };
                    }

                    if eval.value.depth() > DEPTH_LIMIT {
                        eval.value = Type::Any;
                    }

                    (expression, eval)
                })
                .collect();

            new_abstract_state
                .get_mut(&self.qualified_location)
                .expect("evaluation_state should exists")
                .types = new_evaluations;
        }

        Ok(new_abstract_state)
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, Join)]
pub struct ProgramEvaluation {
    pub states: imbl::OrdMap<QualifiedLocation, EvaluationState>,
}

impl ProgramEvaluation {
    pub fn new(states: imbl::OrdMap<QualifiedLocation, EvaluationState>) -> Self {
        Self { states }
    }

    pub fn unit(qualified_location: QualifiedLocation, evaluation_state: EvaluationState) -> Self {
        Self::new(imbl::OrdMap::unit(qualified_location, evaluation_state))
    }

    pub fn update(
        &self,
        qualified_location: QualifiedLocation,
        evaluation_state: EvaluationState,
    ) -> Self {
        Self::new(self.states.update(qualified_location, evaluation_state))
    }
}

impl Display for ProgramEvaluation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_set(f, self.states.iter(), |f, (location, state)| {
            write!(f, "{}: {}", location, state)
        })
    }
}

impl AbstractState for ProgramEvaluation {
    type Key = QualifiedLocation;
    type AbstractValue = EvaluationState;

    fn get(&self, key: &Self::Key) -> Option<&Self::AbstractValue> {
        self.states.get(key)
    }

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::AbstractValue> {
        self.states.get_mut(key)
    }

    fn get_or_insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue {
        self.states.entry(key).or_insert(abstract_value)
    }

    fn insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue {
        match self.states.entry(key) {
            Entry::Occupied(entry) => {
                let previous_abstract_value = entry.into_mut();
                *previous_abstract_value = abstract_value;
                previous_abstract_value
            }
            Entry::Vacant(entry) => entry.insert(abstract_value),
        }
    }
}

pub fn analyse_program_entity<
    'e,
    's: 'e,
    S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Eq,
>(
    abstract_state: &'e mut AbstractStateProxy<'s, S, ProgramEvaluation>,
    program_entity_constraints: &imbl::OrdMap<QualifiedLocation, ProgramEntityConstraints>,
    qualified_location: &'e QualifiedLocation,
) -> Result<&'e mut EvaluationState, Infallible> {
    let solver_state = analysis(
        &ConstraintSolver::new(
            qualified_location,
            program_entity_constraints,
            abstract_state,
        ),
        &mut DummyAnalysisObserver::default(),
    )?;

    let evaluation_state =
        if let Some(program_evaluation) = solver_state.get(&ConstraintNode::TypeExit) {
            let mut evaluation_state = program_evaluation.get_clone_or_default(qualified_location);

            if let Some(exception_evaluation_state) = solver_state
                .get(&ConstraintNode::ExceptionExit)
                .and_then(|program_evaluation| program_evaluation.get(qualified_location))
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
                .and_then(|program_evaluation| program_evaluation.get(qualified_location).cloned())
                .unwrap_or_default()
        };

    let new_abstract_state = solver_state.get(&ConstraintNode::Exit).cloned(); // TODO: should always exist

    drop(solver_state);

    if let Some(new_abstract_state) = new_abstract_state {
        abstract_state.proxy = new_abstract_state.proxy;
    }

    Ok(abstract_state.insert(qualified_location.clone(), evaluation_state))
}

pub struct ModuleConstraintSolver<'a> {
    pub graph:
        &'a DependentGraph<ModuleNode, imbl::OrdMap<QualifiedLocation, ProgramEntityConstraints>>,
}

impl<'a> ModuleConstraintSolver<'a> {
    pub fn new(
        graph: &'a DependentGraph<
            ModuleNode,
            imbl::OrdMap<QualifiedLocation, ProgramEntityConstraints>,
        >,
    ) -> Self {
        Self { graph }
    }
}

impl GraphAnalyser for ModuleConstraintSolver<'_> {
    type Node = ModuleNode;
    type AbstractState = ProgramEvaluation;
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

        let mut proxy = AbstractStateProxy::new(&new_analysis_state, ProgramEvaluation::default());

        let qualified_location = QualifiedLocation::new(module_name.clone(), imbl::Vector::new());

        analyse_program_entity(
            &mut proxy,
            self.graph.nodes.get(&node).unwrap(),
            &qualified_location,
        )?;

        new_analysis_state.extend(proxy.proxy.states);

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
    use crate::abstract_environment::BUILTINS_MODULE;
    use crate::constraints::{ModuleLoader, ModuleName, analyse_program};
    use apy::v1::QualifiedName;
    use apygen_analysis::analysis;
    use apygen_analysis::log::LogAnalysisObserver;
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
            pass

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
            a@{module[4:4]} = 42
            b@{module[8:0]} = 42
            x@{module[1:0]} = True
            #raise = {}
            #return = None
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
            a@{module[1:0]} = 0
            a@{module[4:4]} = Union[Any, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
            b@{module[6:0]} = Any
            #raise = {Exception(type=Any, origin=Unknown)}
            #return = None
        "##},  // TODO: fix this when operations are implemented
    )]
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a: int, b):
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        module:
            add_two@{module[1:4]} = function(add_two@module[1:0])
            result@{module[4:0]} = Never ⊔ #deferred{(add_two@{module[4:9]})(42, 67)}
            #raise = {}
            #return = None
        module[1:0]:
            a@{module[1:12]} = Never ⊔ #deferred{#annotated(int@{module[1:15]})}
            b@{module[1:20]} = Never
            #raise = {} ⊔ #deferred{#annotated(int@{module[1:15]})}
            #return = Never
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
            A@{module[1:6]} = class(A@module[1:0])
            result@{module[4:0]} = 5
            #raise = {}
            #return = None
        module[1:0]:
            b@{module[1:0][2:4]} = 5
            #raise = {}
            #return = None
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
            A@{module[1:6]} = class(A@module[1:0])
            a@{module[4:0]} = @class(A@module[1:0])
            result@{module[5:0]} = 5
            #raise = {}
            #return = None
        module[1:0]:
            b@{module[1:0][2:4]} = 5
            #raise = {}
            #return = None
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
            A@{module[1:6]} = class(A@module[1:0])
            result@{module[5:0]} = function(foo@module[1:0][2:4])
            #raise = {}
            #return = None
        module[1:0]:
            foo@{module[1:0][2:8]} = function(foo@module[1:0][2:4])
            #raise = {}
            #return = None
        module[1:0][2:4]:
            #raise = {}
            #return = 5
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
            A@{module[1:6]} = class(A@module[1:0])
            a@{module[5:0]} = @class(A@module[1:0])
            result@{module[6:0]} = method(class(A@module[1:0])[], function(foo@module[1:0][2:4]))
            #raise = {}
            #return = None
        module[1:0]:
            foo@{module[1:0][2:8]} = function(foo@module[1:0][2:4])
            #raise = {}
            #return = None
        module[1:0][2:4]:
            #raise = {}
            #return = 5
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
            CONST@{module[6:0]} = 5
            foo@{module[1:4]} = function(foo@module[1:0])
            result@{module[4:0]} = Never ⊔ #deferred{(foo@{module[4:9]})()}
            #raise = {}
            #return = None
        module[1:0]:
            #raise = {} ⊔ #deferred{CONST@{module[1:0][2:11]}}
            #return = Never ⊔ #deferred{CONST@{module[1:0][2:11]}}
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
            CONST@{module[4:0]} = 5
            foo@{module[1:4]} = function(foo@module[1:0])
            result@{module[6:0]} = 5
            #raise = {}
            #return = None
        module[1:0]:
            #raise = {}
            #return = 5
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
                    String::new(),
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
            if qualified_location.module_name != module_name {
                continue;
            }
            actual_types.push_str(&format!("{}:\n", qualified_location));
            for (variable, ty) in abstract_state.variables() {
                actual_types.push_str(&format!("    {} = {}\n", variable, ty));
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
