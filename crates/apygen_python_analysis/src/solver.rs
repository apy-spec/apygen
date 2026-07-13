use crate::abstract_environment::{
    BUILTINS_MODULE, ClassType, DEPTH_LIMIT, FunctionType, LiteralClass, LiteralFunction,
    LiteralMethod, RaisedExceptions, StructuralDepth, StructuralWidth, TYPES_MODULE, Type,
    TypeInstance2, TypeLiteral, TypeUnion, WIDTH_LIMIT,
};
use crate::constraints::{
    AbstractEnvironmentSpecification, BinaryOperator, ConstraintGraph, ConstraintNode,
    DependentGraph, Expression, ExpressionAnnotated, ExpressionAttribute, ExpressionBinary,
    ExpressionCall, ExpressionClass, ExpressionFunction, ExpressionVariable, ModuleName,
    ModuleNode, ProgramAnalysis, ProgramEntity, ProgramEntityNode, QualifiedLocation, VariableName,
};
use crate::genkill::calls::Arguments;
use crate::genkill::expressions::literal_class::method_resolution_order;
use crate::genkill::expressions::{PyEffects, PyTypeEval, type_literal};
use crate::{is_type_unreachable, pytype_consume_or_return_option};
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::abstract_state::{AbstractState, AbstractStateProxy};
use apygen_analysis::fmt::{fmt_display_set, fmt_set};
use apygen_analysis::lattice::Join;
use apygen_analysis::log::LogAnalysisObserver;
use apygen_analysis::{GraphAnalyser, analysis};
use imbl::ordmap::Entry;
use std::convert::Infallible;
use std::fmt::{Debug, Display};
use std::sync::Arc;

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Join)]
pub struct DefinedVariables {
    pub names: imbl::OrdMap<VariableName, imbl::OrdSet<QualifiedLocation>>,
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
            fmt_display_set(f, locations.iter())
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Join)]
pub struct ExpressionEval {
    type_eval: PyTypeEval,
    deferred: imbl::OrdSet<Arc<Expression>>,
}

impl ExpressionEval {
    pub fn new(type_eval: PyTypeEval, deferred: imbl::OrdSet<Arc<Expression>>) -> Self {
        Self {
            type_eval,
            deferred,
        }
    }
}

impl Display for ExpressionEval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.deferred.is_empty() {
            write!(f, "{}", self.type_eval)
        } else {
            write!(f, "{} ⊔ #deferred", self.type_eval)?;
            fmt_display_set(f, self.deferred.iter())
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, Join)]
pub struct EvaluationState {
    pub evaluations: imbl::OrdMap<Arc<Expression>, ExpressionEval>,
    pub return_value: imbl::OrdSet<Arc<Expression>>,
    pub raised_exceptions: RaisedExceptions,
    pub defined_variables: DefinedVariables,
}

impl Display for EvaluationState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("(evaluations: ")?;
        fmt_set(f, self.evaluations.iter(), |f, (expression, eval)| {
            write!(f, "{}: {}", expression, eval)
        })?;
        f.write_str(", return: ")?;
        fmt_display_set(f, self.return_value.iter())?;
        write!(
            f,
            ", raised: {}, defined_variables = {})",
            self.raised_exceptions, self.defined_variables
        )
    }
}

impl EvaluationState {
    pub fn variables(&self) -> impl Iterator<Item = (ExpressionVariable, ExpressionEval)> {
        self.defined_variables
            .names
            .iter()
            .flat_map(|(variable, locations)| {
                locations.iter().map(|location| {
                    let expression_variable =
                        ExpressionVariable::new(variable.clone(), location.clone());

                    (
                        expression_variable.clone(),
                        self.evaluations
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

pub struct ConstraintSolver<
    's,
    S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
> {
    pub program_entity: &'s ProgramEntity,
    pub specification: &'s AbstractEnvironmentSpecification,
    pub graph: &'s ConstraintGraph,
    pub program_evaluation: &'s S,
}

impl<'s, S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>>
    ConstraintSolver<'s, S>
{
    pub fn new(
        program_entity: &'s ProgramEntity,
        specification: &'s AbstractEnvironmentSpecification,
        graph: &'s ConstraintGraph,
        program_evaluation: &'s S,
    ) -> Self {
        Self {
            program_entity,
            specification,
            graph,
            program_evaluation,
        }
    }
}

impl<
    's,
    S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Debug + Eq + Clone,
> GraphAnalyser for ConstraintSolver<'s, S>
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
            .graph
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
        let mut program_evaluation = analysis_state.get_clone_or_else(node, || {
            AbstractStateProxy::new(
                self.program_evaluation,
                ProgramEvaluation::unit(
                    self.program_entity.location.clone(),
                    EvaluationState::default(),
                ),
            )
        });

        match &node {
            ConstraintNode::Entry => {
                for (variable, expressions) in self.specification.arguments.as_ref() {
                    let expression_evals =
                        expressions
                            .iter()
                            .fold(ExpressionEval::default(), |acc, expression| {
                                acc.join(&match evaluate_expression(
                                    &program_evaluation,
                                    &self.program_entity.location,
                                    &Arc::new(expression.clone()),
                                ) {
                                    Some(type_eval) => {
                                        ExpressionEval::new(type_eval, imbl::OrdSet::default())
                                    }
                                    None => ExpressionEval::new(
                                        PyTypeEval::never(),
                                        imbl::OrdSet::unit(Arc::new(expression.clone())),
                                    ),
                                })
                            });

                    let evaluation_state = program_evaluation
                        .get_or_insert_default(self.program_entity.location.clone());

                    evaluation_state.defined_variables.names.insert(
                        variable.name.clone(),
                        imbl::OrdSet::unit(variable.location.clone()),
                    );

                    evaluation_state.evaluations.insert(
                        Arc::new(Expression::Variable(variable.clone())),
                        expression_evals,
                    );
                }
            }
            ConstraintNode::TypeConstraint(constraint) => {
                let expression_eval = match evaluate_expression(
                    &program_evaluation,
                    &self.program_entity.location,
                    &constraint.left,
                ) {
                    Some(type_eval) => ExpressionEval::new(type_eval, imbl::OrdSet::default()),
                    None => ExpressionEval::new(
                        PyTypeEval::never(),
                        imbl::OrdSet::unit(constraint.left.clone()),
                    ),
                };

                let evaluation_state =
                    program_evaluation.get_or_insert_default(self.program_entity.location.clone());

                evaluation_state
                    .evaluations
                    .entry(constraint.right.clone())
                    .and_modify(|previous_eval| {
                        *previous_eval = previous_eval.join(&expression_eval)
                    })
                    .or_insert(expression_eval);
            }
            ConstraintNode::DefinedVariableConstraint(expression) => {
                let evaluation_state =
                    program_evaluation.get_or_insert_default(self.program_entity.location.clone());

                evaluation_state.defined_variables.names.insert(
                    expression.name.clone(),
                    imbl::OrdSet::unit(expression.location.clone()),
                );
            }
            ConstraintNode::ReturnConstraint(expression) => {
                let evaluation_state =
                    program_evaluation.get_or_insert_default(self.program_entity.location.clone());

                evaluation_state.return_value = imbl::OrdSet::unit(expression.clone());
            }
            _ => {}
        }

        Ok(program_evaluation)
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
        assert_eq!(left.abstract_state, self.program_evaluation);
        assert_eq!(right.abstract_state, self.program_evaluation);

        let mut new_abstract_state =
            AbstractStateProxy::new(self.program_evaluation, left.proxy.join(&right.proxy));

        simplify(&mut new_abstract_state, &self.program_entity.location);

        if let Some(evaluation_state) = new_abstract_state.get(&self.program_entity.location) {
            let new_evaluations = evaluation_state
                .evaluations
                .clone()
                .into_iter()
                .map(|(expression, mut eval)| {
                    while eval.type_eval.value.width() > WIDTH_LIMIT {
                        eval.type_eval.value = match eval.type_eval.value {
                            Type::Union(type_union) => {
                                let mut new_type_union = TypeUnion::new();
                                for ty in type_union.types() {
                                    new_type_union.add_type(
                                        if let Type::Literal(type_literal) = ty.as_ref() {
                                            Arc::new(
                                                as_type_instance(&new_abstract_state, type_literal)
                                                    .map(|type_instance| {
                                                        Type::Instance2(type_instance)
                                                    })
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

                    if eval.type_eval.value.depth() > DEPTH_LIMIT {
                        eval.type_eval.value = Type::Any;
                    }

                    (expression, eval)
                })
                .collect();

            new_abstract_state
                .get_mut(&self.program_entity.location)
                .expect("evaluation_state should exists")
                .evaluations = new_evaluations;
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

pub fn get_variable_type(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    module_name: &ModuleName,
    name: &VariableName,
) -> Option<TypeInstance2> {
    let evaluation_state = abstract_state.get(&QualifiedLocation::new(
        module_name.clone(),
        imbl::Vector::new(),
    ))?;

    let locations = evaluation_state.defined_variables.names.get(name)?;

    let mut base = Type::Never;

    for location in locations {
        base = base.join(
            &evaluation_state
                .evaluations
                .get(&Expression::Variable(ExpressionVariable::new(
                    name.clone(),
                    location.clone(),
                )))?
                .type_eval
                .value,
        );
    }

    if base == Type::Never {
        return None;
    }

    Some(TypeInstance2 {
        base: Arc::new(base),
        arguments: imbl::Vector::new(),
    })
}

pub fn as_type_instance(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    ty: &TypeLiteral,
) -> Option<TypeInstance2> {
    match ty {
        TypeLiteral::Integer(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("int")),
        ),
        TypeLiteral::Boolean(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("bool")),
        ),
        TypeLiteral::Float(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("float")),
        ),
        TypeLiteral::Complex(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("complex")),
        ),
        TypeLiteral::String(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("str")),
        ),
        TypeLiteral::Bytes(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("bytes")),
        ),
        TypeLiteral::None => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(TYPES_MODULE)),
            &Arc::new(Identifier::parse("NoneType")),
        ),
        TypeLiteral::Ellipsis => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(TYPES_MODULE)),
            &Arc::new(Identifier::parse("EllipsisType")),
        ),
        TypeLiteral::List(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("list")),
        ),
        TypeLiteral::Tuple(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("tuple")),
        ),
        TypeLiteral::Dict(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("dict")),
        ),
        TypeLiteral::Function(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(TYPES_MODULE)),
            &Arc::new(Identifier::parse("FunctionType")),
        ),
        TypeLiteral::OverloadedFunction(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(TYPES_MODULE)),
            &Arc::new(Identifier::parse("FunctionType")),
        ),
        TypeLiteral::Method(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(TYPES_MODULE)),
            &Arc::new(Identifier::parse("MethodType")),
        ),
        TypeLiteral::Class(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
            &Arc::new(Identifier::parse("type")),
        ),
        TypeLiteral::TypeAlias(_) => None,
        TypeLiteral::Generic(_) => None,
        TypeLiteral::ImportedModule(_) => get_variable_type(
            abstract_state,
            &Arc::new(QualifiedName::parse(TYPES_MODULE)),
            &Arc::new(Identifier::parse("ModuleType")),
        ),
    }
}

pub fn simplify(
    abstract_state: &mut impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    current_program_entity: &QualifiedLocation,
) -> Option<()> {
    let mut evaluations = abstract_state
        .get(&current_program_entity)?
        .evaluations
        .clone();

    loop {
        let mut changed = false;

        evaluations = evaluations
            .into_iter()
            .map(|(expression, evaluation)| {
                let mut eval =
                    ExpressionEval::new(evaluation.type_eval.clone(), imbl::OrdSet::default());

                for expression in &evaluation.deferred {
                    match evaluate_expression(abstract_state, &current_program_entity, &expression)
                    {
                        Some(type_eval) => {
                            eval.type_eval = eval.type_eval.join(&type_eval);
                            changed = true;
                        }
                        None => {
                            eval.deferred.insert(expression.clone());
                        }
                    }
                }

                (expression, eval)
            })
            .collect();

        let evaluation_state = abstract_state
            .get_mut(current_program_entity)
            .expect("evaluation_state should exists");

        evaluation_state.evaluations = evaluations.clone();

        if !changed {
            break;
        }
    }

    Some(())
}

pub fn evaluate_expression_eval(expression_eval: &ExpressionEval) -> Option<PyTypeEval> {
    if expression_eval.deferred.is_empty() {
        Some(expression_eval.type_eval.clone())
    } else {
        None
    }
}

pub fn evaluate_expression_variable(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    current_program_entity: &QualifiedLocation,
    expression_variable: &ExpressionVariable,
) -> Option<PyTypeEval> {
    let parent_location = expression_variable.location.at_parent_location().unwrap();

    let evaluation_state = abstract_state.get(&parent_location)?;

    let Some(evaluation) = evaluation_state
        .evaluations
        .get(&Expression::Variable(expression_variable.clone()))
    else {
        return if evaluation_state
            .defined_variables
            .names
            .contains_key(&expression_variable.name)
        {
            Some(PyTypeEval::with_default_effects(Type::Never))
        } else {
            Some(PyTypeEval::with_default_effects(Type::Never)) // TODO: Add exceptions
        };
    };

    evaluate_expression_eval(evaluation)
}

pub fn evaluate_expression_annotated(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    current_program_entity: &QualifiedLocation,
    expression_annotated: &ExpressionAnnotated,
) -> Option<PyTypeEval> {
    let annotation_eval = evaluate_expression(
        abstract_state,
        current_program_entity,
        &expression_annotated.annotation,
    )?;

    Some(PyTypeEval::with_default_effects(Type::Instance2(
        TypeInstance2 {
            base: Arc::new(annotation_eval.value.clone()),
            arguments: imbl::Vector::new(),
        },
    )))
}

pub fn evaluate_expression_function(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    current_program_entity: &QualifiedLocation,
    expression_function: &ExpressionFunction,
) -> Option<PyTypeEval> {
    Some(PyTypeEval::with_default_effects(Type::new_literal(
        TypeLiteral::Function(LiteralFunction {
            value: Arc::new(FunctionType {
                name: Arc::new(Identifier::parse("todo")),
                location: apygen_analysis::namespace::Location::at_exit(
                    apygen_analysis::namespace::NamespaceLocation::from(Arc::new(
                        QualifiedName::parse("todo"),
                    )),
                ),
                qualified_location: expression_function.location.clone(),
                generics: Default::default(),
                parameters: Default::default(),
                is_async: expression_function.is_async,
            }),
        }),
    )))
}

pub fn evaluate_expression_class(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    current_program_entity: &QualifiedLocation,
    expression_class: &ExpressionClass,
) -> Option<PyTypeEval> {
    Some(PyTypeEval::with_default_effects(Type::new_literal(
        TypeLiteral::Class(LiteralClass {
            value: Arc::new(ClassType {
                name: Arc::new(Identifier::parse("todo")),
                location: apygen_analysis::namespace::Location::at_exit(
                    apygen_analysis::namespace::NamespaceLocation::from(Arc::new(
                        QualifiedName::parse("todo"),
                    )),
                ),
                qualified_location: expression_class.location.clone(),
                generics: Default::default(),
                bases: Default::default(),
                keyword_arguments: Default::default(),
                is_abstract: false,
            }),
        }),
    )))
}

pub fn evaluate_expression_attribute(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    current_program_entity: &QualifiedLocation,
    expression_attribute: &ExpressionAttribute,
) -> Option<PyTypeEval> {
    let mut effects = PyEffects::new();

    let value_ty = pytype_consume_or_return_option!(
        effects,
        evaluate_expression(
            abstract_state,
            current_program_entity,
            &expression_attribute.value
        )?
    );

    /// References: https://docs.python.org/3/howto/descriptor.html
    pub fn evaluate_attributes(
        abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
        value_ty: &Type,
        name: &VariableName,
        instance_arguments: Option<&imbl::Vector<Arc<Type>>>,
    ) -> Option<PyTypeEval> {
        match value_ty {
            Type::Instance2(type_instance) => evaluate_attributes(
                abstract_state,
                &type_instance.base,
                name,
                Some(&type_instance.arguments),
            ),
            Type::Union(type_union) => {
                let mut eval = PyTypeEval::never();
                for ty in type_union.types() {
                    eval = eval.join(&evaluate_attributes(abstract_state, ty, name, None)?);
                }
                Some(eval)
            }
            Type::Intersection(type_intersection) => {
                let mut eval = PyTypeEval::never();
                for ty in type_intersection {
                    eval = eval.join(&evaluate_attributes(abstract_state, ty, name, None)?);
                }
                Some(eval)
            }
            Type::Literal(type_literal) => match type_literal.as_ref() {
                TypeLiteral::Class(literal_class) => {
                    // TODO: add support for descriptors
                    for class in method_resolution_order(literal_class)? {
                        let Some(state) = abstract_state.get(&class.value.qualified_location)
                        else {
                            continue;
                        };

                        let Some(locations) = state.defined_variables.names.get(name) else {
                            continue;
                        };

                        let mut eval = PyTypeEval::never();
                        for location in locations {
                            let location_eval = state.evaluations.get(&Expression::Variable(
                                ExpressionVariable::new(name.clone(), location.clone()),
                            ))?;
                            if !location_eval.deferred.is_empty() {
                                return None;
                            }
                            eval = eval.join(&location_eval.type_eval.clone().map(|ty| {
                                let Type::Literal(type_literal) = &ty else {
                                    return ty;
                                };
                                let TypeLiteral::Function(literal_function) = type_literal.as_ref()
                                else {
                                    return ty;
                                };
                                let Some(arguments) = instance_arguments else {
                                    return ty;
                                };

                                Type::new_literal(TypeLiteral::Method(LiteralMethod {
                                    class: class.value.clone(),
                                    function: literal_function.value.clone(),
                                    arguments: arguments.clone(),
                                }))
                            }));
                        }

                        return Some(eval);
                    }
                    None
                }
                _ => evaluate_attributes(
                    abstract_state,
                    &Type::Instance2(as_type_instance(abstract_state, type_literal)?),
                    name,
                    None,
                ),
            },
            _ => None,
        }
    }

    evaluate_attributes(
        abstract_state,
        &value_ty,
        &expression_attribute.attribute,
        None,
    )
}

pub fn evaluate_expression_call(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    current_program_entity: &QualifiedLocation,
    expression_call: &ExpressionCall,
) -> Option<PyTypeEval> {
    let mut effects = PyEffects::new();

    let literal_ty = pytype_consume_or_return_option!(
        effects,
        evaluate_expression(
            abstract_state,
            current_program_entity,
            &expression_call.target
        )?
    );

    let mut arguments = Arguments::new();

    for argument in &expression_call.positional_arguments {
        let argument_ty = pytype_consume_or_return_option!(
            effects,
            evaluate_expression(abstract_state, current_program_entity, &argument)?
        );

        arguments.positional.push(Arc::new(argument_ty));
    }
    for keyword_argument in &expression_call.keyword_arguments {
        if let Some(name) = &keyword_argument.name {
            let keyword_argument_ty = pytype_consume_or_return_option!(
                effects,
                evaluate_expression(
                    abstract_state,
                    current_program_entity,
                    &keyword_argument.value
                )?
            );

            arguments
                .keyword
                .insert(name.clone(), Arc::new(keyword_argument_ty));
        }
    }

    let Type::Literal(literal) = &literal_ty else {
        return None; // TODO: add support for unions, etc
    };

    match literal.as_ref() {
        TypeLiteral::Function(literal_function) => abstract_state
            .get(&literal_function.value.qualified_location)
            .map(|evaluation_state| {
                let ty = evaluation_state.return_value.iter().try_fold(
                    Type::Never,
                    |acc, expression| {
                        let expression_eval = evaluation_state.evaluations.get(expression)?;

                        if expression_eval.deferred.is_empty() {
                            None
                        } else {
                            Some(acc.join(&expression_eval.type_eval.value))
                        }
                    },
                )?;
                Some(PyTypeEval::new(
                    ty,
                    PyEffects::new().with_exceptions(evaluation_state.raised_exceptions.clone()),
                ))
            })
            .unwrap_or_default(),
        TypeLiteral::Class(_) => Some(PyTypeEval::with_default_effects(Type::Instance2(
            TypeInstance2 {
                base: Arc::new(literal_ty.clone()),
                arguments: imbl::Vector::new(),
            },
        ))),
        _ => None, // TODO: add support for classes, etc
    }
}

pub fn evaluate_expression_binary(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    current_program_entity: &QualifiedLocation,
    expression_binary: &ExpressionBinary,
) -> Option<PyTypeEval> {
    let mut effects = PyEffects::new();

    let left_ty = pytype_consume_or_return_option!(
        effects,
        evaluate_expression(
            abstract_state,
            current_program_entity,
            &expression_binary.left
        )?
    );
    let right_ty = pytype_consume_or_return_option!(
        effects,
        evaluate_expression(
            abstract_state,
            current_program_entity,
            &expression_binary.right
        )?
    );

    pub fn evaluate_binary_operation(
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
                    type_eval = type_eval.join(&evaluate_binary_operation(ty, operator, right_ty)?);
                }
                for ty in right_type_union.types() {
                    type_eval = type_eval.join(&evaluate_binary_operation(left_ty, operator, ty)?);
                }
                Some(type_eval)
            }
            (Type::Union(left_type_union), _) => {
                let mut type_eval = PyTypeEval::never();
                for ty in left_type_union.types() {
                    type_eval = type_eval.join(&evaluate_binary_operation(ty, operator, right_ty)?);
                }
                Some(type_eval)
            }
            (_, Type::Union(right_type_union)) => {
                let mut type_eval = PyTypeEval::never();
                for ty in right_type_union.types() {
                    type_eval = type_eval.join(&evaluate_binary_operation(left_ty, operator, ty)?);
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

    let ty = pytype_consume_or_return_option!(
        effects,
        evaluate_binary_operation(&left_ty, expression_binary.operator, &right_ty)?
    );

    Some(PyTypeEval::new(ty, effects))
}

pub fn evaluate_expression(
    abstract_state: &impl AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
    current_program_entity: &QualifiedLocation,
    expression: &Arc<Expression>,
) -> Option<PyTypeEval> {
    if let Some(expression_eval) = abstract_state
        .get(current_program_entity)
        .and_then(|state| state.evaluations.get(expression))
    {
        return evaluate_expression_eval(expression_eval);
    }

    match expression.as_ref() {
        Expression::Variable(expression_variable) => evaluate_expression_variable(
            abstract_state,
            current_program_entity,
            expression_variable,
        ),
        Expression::Annotated(expression_annotated) => evaluate_expression_annotated(
            abstract_state,
            current_program_entity,
            expression_annotated,
        ),
        Expression::Override(_) => None,
        Expression::Function(expression_function) => evaluate_expression_function(
            abstract_state,
            current_program_entity,
            expression_function,
        ),
        Expression::Class(expression_class) => {
            evaluate_expression_class(abstract_state, current_program_entity, expression_class)
        }
        Expression::Import(_) => None,
        Expression::Attribute(expression_attribute) => evaluate_expression_attribute(
            abstract_state,
            current_program_entity,
            expression_attribute,
        ),
        Expression::Subscript(_) => None,
        Expression::Call(expression_call) => {
            evaluate_expression_call(abstract_state, current_program_entity, expression_call)
        }
        Expression::Unary(_) => None,
        Expression::Binary(expression_binary) => {
            evaluate_expression_binary(abstract_state, current_program_entity, expression_binary)
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
        Expression::LiteralEllipsis => Some(PyTypeEval::with_default_effects(Type::new_literal(
            TypeLiteral::Ellipsis,
        ))),
    }
}

pub struct ProgramEntityConstraintSolver<
    's,
    S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>,
> {
    pub module_node: &'s ModuleNode,
    pub graph: &'s DependentGraph<ProgramEntityNode, ProgramAnalysis>,
    pub program_evaluation: &'s S,
}

impl<'s, S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState>>
    ProgramEntityConstraintSolver<'s, S>
{
    pub fn new(
        module_node: &'s ModuleNode,
        graph: &'s DependentGraph<ProgramEntityNode, ProgramAnalysis>,
        program_evaluation: &'s S,
    ) -> Self {
        Self {
            module_node,
            graph,
            program_evaluation,
        }
    }
}

impl<
    's,
    S: AbstractState<Key = QualifiedLocation, AbstractValue = EvaluationState> + Debug + Eq + Clone,
> GraphAnalyser for ProgramEntityConstraintSolver<'s, S>
{
    type Node = ProgramEntityNode;
    type AbstractState = AbstractStateProxy<'s, S, ProgramEvaluation>;
    type AnalysisState = SolverState<Self::Node, Self::AbstractState>;
    type Error = Infallible;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error> {
        Ok(std::iter::once(ProgramEntityNode::Entry))
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
        let mut previous_state = analysis_state.get_clone_or_else(node, || {
            AbstractStateProxy::with_default_proxy(self.program_evaluation)
        });

        let ProgramEntityNode::Entity(entity) = &node else {
            return Ok(previous_state);
        };

        let abstract_environment = self.graph.nodes.get(&node).unwrap();

        let solver_state = analysis(
            &ConstraintSolver::new(
                &entity,
                &abstract_environment.specification,
                &abstract_environment.constraint_graph,
                &previous_state,
            ),
            &mut LogAnalysisObserver::with_prefix(node.to_string()),
        )?;

        let program_evaluation =
            if let Some(program_evaluation) = solver_state.get(&ConstraintNode::TypeExit) {
                program_evaluation.proxy.clone()
            } else {
                ProgramEvaluation::default()
            };

        let mut evaluation_state = program_evaluation.get_clone_or_default(&entity.location);

        if let Some(exception_program_evaluation) = solver_state.get(&ConstraintNode::ExceptionExit)
        {
            let exception_evaluation_state = exception_program_evaluation
                .proxy
                .get_clone_or_default(&entity.location);

            evaluation_state.evaluations = evaluation_state
                .evaluations
                .join(&exception_evaluation_state.evaluations);
            evaluation_state.raised_exceptions = evaluation_state
                .raised_exceptions
                .join(&exception_evaluation_state.raised_exceptions);
        }

        drop(solver_state);

        previous_state
            .proxy
            .insert(entity.location.clone(), evaluation_state);

        Ok(previous_state)
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
        node: &Self::Node,
        left: &Self::AbstractState,
        right: &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error> {
        assert_eq!(left.abstract_state, self.program_evaluation);
        assert_eq!(right.abstract_state, self.program_evaluation);

        let mut new_abstract_state =
            AbstractStateProxy::new(self.program_evaluation, left.proxy.join(&right.proxy));

        if let ProgramEntityNode::Entity(entity) = &node {
            simplify(&mut new_abstract_state, &entity.location);
        }

        Ok(new_abstract_state)
    }
}

pub struct ModuleConstraintSolver<'a> {
    pub graph: &'a DependentGraph<ModuleNode, DependentGraph<ProgramEntityNode, ProgramAnalysis>>,
}

impl<'a> ModuleConstraintSolver<'a> {
    pub fn new(
        graph: &'a DependentGraph<ModuleNode, DependentGraph<ProgramEntityNode, ProgramAnalysis>>,
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
        let mut previous_state = analysis_state.get_clone_or_default(node);

        if let Some(dependent_graph) = self.graph.nodes.get(&node) {
            let solver_state = analysis(
                &ProgramEntityConstraintSolver::new(&node, dependent_graph, &previous_state),
                &mut LogAnalysisObserver::with_prefix(node.to_string()),
            )?;

            let program_evaluation =
                if let Some(program_evaluation) = solver_state.get(&ProgramEntityNode::Exit) {
                    program_evaluation.proxy.clone()
                } else {
                    ProgramEvaluation::default()
                };

            drop(solver_state);

            previous_state.states.extend(program_evaluation.states);
        }

        Ok(previous_state)
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
        node: &Self::Node,
        left: &Self::AbstractState,
        right: &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error> {
        let mut new_abstract_state = left.join(right);

        if let Some(dependent_graph) = self.graph.nodes.get(&node) {
            for node in dependent_graph.nodes.keys() {
                if let ProgramEntityNode::Entity(entity) = &node {
                    simplify(&mut new_abstract_state, &entity.location);
                }
            }
        }

        Ok(new_abstract_state)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abstract_environment::BUILTINS_MODULE;
    use crate::constraints::{CfgImporter, ModuleName, analyse_program};
    use apy::v1::QualifiedName;
    use apygen_analysis::analysis;
    use apygen_analysis::cfg::Cfg;
    use apygen_analysis::log::LogAnalysisObserver;
    use indoc::indoc;
    use rstest::rstest;
    use std::collections::{HashMap, HashSet};

    fn init_logger() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    pub struct TestCfgImporter {
        pub modules: HashMap<ModuleName, Cfg>,
    }

    impl CfgImporter for TestCfgImporter {
        fn import_cfg(&self, module_name: &ModuleName) -> Option<Cfg> {
            self.modules.get(module_name).cloned()
        }
    }

    const TEST_BUILTINS: &str = indoc! {r##"
        class int:
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
        builtins:
            int@{builtins[1:6]} = (class(builtins[1:6]) ➤ ({} - Pure - Total))
            #return = {}
        builtins[1:6]:
            #return = {}
        module:
            a@{module[4:4]} = (42 ➤ ({} - Pure - Total))
            a@{module[6:4]} = (67 ➤ ({} - Pure - Total))
            b@{module[8:0]} = (Union[42, 67] ➤ ({} - Pure - Total))
            x@{module[1:0]} = (True ➤ ({} - Pure - Total))
            #return = {}
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
        builtins:
            int@{builtins[1:6]} = (class(builtins[1:6]) ➤ ({} - Pure - Total))
            #return = {}
        builtins[1:6]:
            #return = {}
        module:
            a@{module[1:0]} = (0 ➤ ({} - Pure - Total))
            a@{module[4:4]} = (Union[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] ➤ ({} - Pure - Total)) ⊔ #deferred{(a@{module[4:8]}) + (1)}
            b@{module[6:0]} = (Union[@class(builtins[1:6]), 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ➤ ({} - Pure - Total)) ⊔ #deferred{a@{module[6:4]}}
            #return = {}
        "##},  // TODO: fix this when operations are implemented
    )]
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a: int, b):
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        builtins:
            int@{builtins[1:6]} = (class(builtins[1:6]) ➤ ({} - Pure - Total))
            #return = {}
        builtins[1:6]:
            #return = {}
        module:
            add_two@{module[1:4]} = (function(module[1:4]) ➤ ({} - Pure - Total))
            result@{module[4:0]} = (Never ➤ ({} - Pure - Total)) ⊔ #deferred{(add_two@{module[4:9]})(42, 67)}
            #return = {}
        module[1:4]:
            a@{module[1:12]} = (@class(builtins[1:6]) ➤ ({} - Pure - Total))
            b@{module[1:20]} = (Never ➤ ({} - Pure - Total))
            #return = {(a@{module[1:4][2:11]}) + (b@{module[1:4][2:15]})}
        "##},
    )]
    #[case::simple_class_attribute_access(
        indoc! {r##"
        class A:
            b = 5

        result = A.b
        "##},
        indoc! {r##"
        builtins:
            int@{builtins[1:6]} = (class(builtins[1:6]) ➤ ({} - Pure - Total))
            #return = {}
        builtins[1:6]:
            #return = {}
        module:
            A@{module[1:6]} = (class(module[1:6]) ➤ ({} - Pure - Total))
            result@{module[4:0]} = (5 ➤ ({} - Pure - Total))
            #return = {}
        module[1:6]:
            b@{module[1:6][2:4]} = (5 ➤ ({} - Pure - Total))
            #return = {}
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
        builtins:
            int@{builtins[1:6]} = (class(builtins[1:6]) ➤ ({} - Pure - Total))
            #return = {}
        builtins[1:6]:
            #return = {}
        module:
            A@{module[1:6]} = (class(module[1:6]) ➤ ({} - Pure - Total))
            a@{module[4:0]} = (@class(module[1:6]) ➤ ({} - Pure - Total))
            result@{module[5:0]} = (5 ➤ ({} - Pure - Total))
            #return = {}
        module[1:6]:
            b@{module[1:6][2:4]} = (5 ➤ ({} - Pure - Total))
            #return = {}
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
        builtins:
            int@{builtins[1:6]} = (class(builtins[1:6]) ➤ ({} - Pure - Total))
            #return = {}
        builtins[1:6]:
            #return = {}
        module:
            A@{module[1:6]} = (class(module[1:6]) ➤ ({} - Pure - Total))
            result@{module[5:0]} = (function(module[1:6][2:8]) ➤ ({} - Pure - Total))
            #return = {}
        module[1:6]:
            foo@{module[1:6][2:8]} = (function(module[1:6][2:8]) ➤ ({} - Pure - Total))
            #return = {}
        module[1:6][2:8]:
            #return = {5}
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
        builtins:
            int@{builtins[1:6]} = (class(builtins[1:6]) ➤ ({} - Pure - Total))
            #return = {}
        builtins[1:6]:
            #return = {}
        module:
            A@{module[1:6]} = (class(module[1:6]) ➤ ({} - Pure - Total))
            a@{module[5:0]} = (@class(module[1:6]) ➤ ({} - Pure - Total))
            result@{module[6:0]} = (method(class(module[1:6])[], function(module[1:6][2:8])) ➤ ({} - Pure - Total))
            #return = {}
        module[1:6]:
            foo@{module[1:6][2:8]} = (function(module[1:6][2:8]) ➤ ({} - Pure - Total))
            #return = {}
        module[1:6][2:8]:
            #return = {5}
        "##},
    )]
    fn test_constraints_solving(#[case] source: &str, #[case] expected_types: &str) {
        init_logger();

        let module_name = Arc::new(QualifiedName::parse("module"));
        let cfg = Cfg::parse(source).expect("Should build CFG");

        let cfg_importer = TestCfgImporter {
            modules: HashMap::from_iter([
                (module_name.clone(), cfg),
                (
                    Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                    Cfg::parse(TEST_BUILTINS).expect("Should build CFG"),
                ),
            ]),
        };
        let dependent_graph = analyse_program(&cfg_importer, HashSet::from_iter([module_name]));

        let solver = ModuleConstraintSolver::new(&dependent_graph);

        let mut program_evaluation = analysis(&solver, &mut LogAnalysisObserver::default())
            .expect("analysis should work")
            .abstract_states[&ModuleNode::Exit]
            .clone();

        for location in program_evaluation
            .states
            .keys()
            .cloned()
            .collect::<Vec<_>>()
        {
            simplify(&mut program_evaluation, &location);
        }

        let mut actual_types = String::new();
        for (node, abstract_state) in program_evaluation.states.as_ref() {
            actual_types.push_str(&format!("{}:\n", node));
            for (variable, ty) in abstract_state.variables() {
                actual_types.push_str(&format!("    {} = {}\n", variable, ty));
            }
            actual_types.push_str("    #return = {");
            for (i, expression) in abstract_state.return_value.iter().enumerate() {
                if i > 0 {
                    actual_types.push_str(", ");
                }
                actual_types.push_str(&format!("{}", expression));
            }
            actual_types.push_str("}\n");
        }

        assert_eq!(expected_types, actual_types, "{actual_types}");
    }
}
