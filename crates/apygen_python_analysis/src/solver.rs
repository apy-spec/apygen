use crate::abstract_environment::{
    ClassType, Completeness, FunctionType, LiteralClass, LiteralFunction, RaisedExceptions, Type,
    TypeInstance2, TypeLiteral,
};
use crate::constraints::{
    AbstractEnvironmentSpecification, ConstraintGraph, ConstraintNode, DependentGraph, Expression,
    ExpressionAnnotated, ExpressionBinary, ExpressionCall, ExpressionClass, ExpressionFunction,
    ExpressionVariable, IncludeConstraint, LatticeMap, ModuleNode, ProgramAnalysis, ProgramEntity,
    ProgramEntityNode, QualifiedLocation, VariableName,
};
use crate::genkill::assignment::AssignmentTarget;
use crate::genkill::calls::Arguments;
use crate::genkill::expressions::{
    PyEffects, PyTypeEval, PyValueEval, gen_arguments, gen_expr, literal_class, literal_function,
    type_literal,
};
use crate::is_type_unreachable;
use crate::{pytype_consume_or_return, pytype_return_unreachable};
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::lattice::Lattice;
use apygen_analysis::{GraphAnalyser, analysis};
use log::{debug, info};
use std::collections::BTreeSet;
use std::convert::Infallible;
use std::sync::Arc;
use std::time::Instant;

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefinedVariables {
    pub names: imbl::OrdMap<VariableName, imbl::OrdSet<QualifiedLocation>>,
}

impl DefinedVariables {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Lattice for DefinedVariables {
    fn includes(&self, other: &Self) -> bool {
        self.names
            .is_submap_by(&other.names, |self_locations, other_locations| {
                other_locations.is_subset(self_locations)
            })
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            names: self
                .names
                .clone()
                .intersection_with(other.names.clone(), |self_locations, other_locations| {
                    self_locations.union(other_locations)
                }),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct EvaluationState {
    pub evaluations: LatticeMap<Arc<Expression>, PyTypeEval>,
    pub return_value: Type,
    pub raised_exceptions: RaisedExceptions,
    pub defined_variables: DefinedVariables,
}

impl EvaluationState {
    pub fn variables(&self) -> impl Iterator<Item = (ExpressionVariable, Type)> {
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
                            .map(|eval| eval.value.clone())
                            .unwrap_or_default(),
                    )
                })
            })
    }
}

impl Lattice for EvaluationState {
    fn includes(&self, other: &Self) -> bool {
        self.evaluations.includes(&other.evaluations)
            && self.return_value.includes(&other.return_value)
            && self.raised_exceptions.includes(&other.raised_exceptions)
            && self.defined_variables.includes(&other.defined_variables)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            evaluations: self.evaluations.join(&other.evaluations),
            return_value: self.return_value.join(&other.return_value),
            raised_exceptions: self.raised_exceptions.join(&other.raised_exceptions),
            defined_variables: self.defined_variables.join(&other.defined_variables),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct SolverState {
    pub evaluation_states: LatticeMap<ConstraintNode, EvaluationState>,
}

impl SolverState {
    pub fn new(evaluation_states: LatticeMap<ConstraintNode, EvaluationState>) -> Self {
        Self { evaluation_states }
    }

    pub fn clone_abstract_state_or_default(&self, node: &ConstraintNode) -> EvaluationState {
        self.evaluation_states
            .get(node)
            .cloned()
            .unwrap_or_default()
    }
}

impl Lattice for SolverState {
    fn includes(&self, other: &Self) -> bool {
        self.evaluation_states.includes(&other.evaluation_states)
    }

    fn join(&self, other: &Self) -> Self {
        Self::new(self.evaluation_states.join(&other.evaluation_states))
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ExitEvaluationStates {
    pub type_evaluation_state: EvaluationState,
    pub exception_evaluation_state: EvaluationState,
}

impl Lattice for ExitEvaluationStates {
    fn includes(&self, other: &Self) -> bool {
        self.type_evaluation_state
            .includes(&other.type_evaluation_state)
            && self
                .exception_evaluation_state
                .includes(&other.exception_evaluation_state)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            type_evaluation_state: self
                .type_evaluation_state
                .join(&other.type_evaluation_state),
            exception_evaluation_state: self
                .exception_evaluation_state
                .join(&other.exception_evaluation_state),
        }
    }
}

pub struct ConstraintSolver<'a> {
    pub program_entity_node: &'a ProgramEntityNode,
    pub specification: &'a AbstractEnvironmentSpecification,
    pub graph: &'a ConstraintGraph,
    pub state: &'a LatticeMap<QualifiedLocation, ExitEvaluationStates>,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(
        program_entity_node: &'a ProgramEntityNode,
        specification: &'a AbstractEnvironmentSpecification,
        graph: &'a ConstraintGraph,
        state: &'a LatticeMap<QualifiedLocation, ExitEvaluationStates>,
    ) -> Self {
        Self {
            program_entity_node,
            specification,
            graph,
            state,
        }
    }

    pub fn evaluate_expression_variable(
        &self,
        abstract_state: &EvaluationState,
        expression_variable: &ExpressionVariable,
    ) -> PyTypeEval {
        let Some(exit_evaluation_states) = self
            .state
            .get(&expression_variable.location.at_parent_location().unwrap())
        else {
            return PyTypeEval::new(
                Type::Never,
                PyEffects::new().with_completeness(Completeness::Partial),
            );
        };
        let Some(ty) = exit_evaluation_states
            .type_evaluation_state
            .evaluations
            .get(&Expression::Variable(expression_variable.clone()))
        else {
            return PyTypeEval::new(
                Type::Never,
                PyEffects::new().with_completeness(Completeness::Partial),
            );
        };

        PyTypeEval::with_default_effects(ty.value.clone())
    }

    pub fn evaluate_expression_annotated(
        &self,
        abstract_state: &EvaluationState,
        expression_annotated: &ExpressionAnnotated,
    ) -> PyTypeEval {
        let annotation_eval =
            self.evaluate_expression(abstract_state, &expression_annotated.annotation);

        PyTypeEval::with_default_effects(Type::Instance2(TypeInstance2 {
            base: Arc::new(annotation_eval.value.clone()),
            arguments: imbl::Vector::new(),
        }))
    }

    pub fn evaluate_expression_function(
        &self,
        abstract_state: &EvaluationState,
        expression_function: &ExpressionFunction,
    ) -> PyTypeEval {
        PyTypeEval::with_default_effects(Type::new_literal(TypeLiteral::Function(
            LiteralFunction {
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
            },
        )))
    }

    pub fn evaluate_expression_class(
        &self,
        abstract_state: &EvaluationState,
        expression_class: &ExpressionClass,
    ) -> PyTypeEval {
        PyTypeEval::with_default_effects(Type::new_literal(TypeLiteral::Class(LiteralClass {
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
        })))
    }

    pub fn evaluate_expression_call(
        &self,
        abstract_state: &EvaluationState,
        expression_call: &ExpressionCall,
    ) -> PyTypeEval {
        let mut effects = PyEffects::new();

        let literal_ty = pytype_consume_or_return!(
            effects,
            self.evaluate_expression(abstract_state, &expression_call.target)
        );

        let Type::Literal(literal) = literal_ty else {
            return PyTypeEval::unknown().extend_effects(&effects);
        };

        let mut arguments = Arguments::new();

        for argument in &expression_call.positional_arguments {
            let argument_ty = pytype_consume_or_return!(
                effects,
                self.evaluate_expression(abstract_state, &argument)
            );

            arguments.positional.push(Arc::new(argument_ty));
        }
        for keyword_argument in &expression_call.keyword_arguments {
            if let Some(name) = &keyword_argument.name {
                let keyword_argument_ty = pytype_consume_or_return!(
                    effects,
                    self.evaluate_expression(abstract_state, &keyword_argument.value)
                );

                arguments
                    .keyword
                    .insert(name.clone(), Arc::new(keyword_argument_ty));
            }
        }

        match literal.as_ref() {
            TypeLiteral::Function(literal_function) => self
                .state
                .get(&literal_function.value.qualified_location)
                .map(|exit_states| {
                    PyTypeEval::new(
                        exit_states.type_evaluation_state.return_value.clone(),
                        PyEffects::new().with_exceptions(
                            exit_states
                                .exception_evaluation_state
                                .raised_exceptions
                                .clone(),
                        ),
                    )
                })
                .unwrap_or_else(|| PyTypeEval::unknown().extend_effects(&effects)),
            _ => PyTypeEval::unknown().extend_effects(&effects),
        }
    }

    pub fn evaluate_expression_binary(
        &self,
        abstract_state: &EvaluationState,
        type_expression: &ExpressionBinary,
    ) -> PyTypeEval {
        let mut effects = PyEffects::new();

        let left_ty = pytype_consume_or_return!(
            effects,
            self.evaluate_expression(abstract_state, &type_expression.left)
        );
        let right_ty = pytype_consume_or_return!(
            effects,
            self.evaluate_expression(abstract_state, &type_expression.right)
        );

        let ty = pytype_consume_or_return!(
            effects,
            match (left_ty, right_ty) {
                (Type::Literal(left), Type::Literal(right)) => {
                    type_literal::call_binary_op(
                        left.as_ref(),
                        type_expression.operator,
                        right.as_ref(),
                    )
                }
                (Type::Any, _) | (_, Type::Any) => PyTypeEval::unknown(),
                _ => PyTypeEval::unknown(),
            }
        );

        PyTypeEval::new(ty, effects)
    }

    pub fn evaluate_expression(
        &self,
        abstract_state: &EvaluationState,
        expression: &Expression,
    ) -> PyTypeEval {
        if let Some(eval) = abstract_state.evaluations.values.get(expression) {
            return eval.clone();
        }

        match expression {
            Expression::Variable(expression_variable) => {
                self.evaluate_expression_variable(abstract_state, expression_variable)
            }
            Expression::Annotated(expression_annotated) => {
                self.evaluate_expression_annotated(abstract_state, expression_annotated)
            }
            Expression::Override(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Function(expression_function) => {
                self.evaluate_expression_function(abstract_state, expression_function)
            }
            Expression::Class(expression_class) => {
                self.evaluate_expression_class(abstract_state, expression_class)
            }
            Expression::Import(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Attribute(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Subscript(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Call(expression_call) => {
                self.evaluate_expression_call(abstract_state, expression_call)
            }
            Expression::Unary(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Binary(expression_binary) => {
                self.evaluate_expression_binary(abstract_state, expression_binary)
            }
            Expression::LiteralInteger(literal_integer) => {
                PyTypeEval::with_default_effects(Type::new_integer_literal(literal_integer.clone()))
            }
            Expression::LiteralFloat(literal_float) => {
                PyTypeEval::with_default_effects(Type::new_float_literal(literal_float.clone()))
            }
            Expression::LiteralComplex(literal_complex) => {
                PyTypeEval::with_default_effects(Type::new_complex_literal(literal_complex.clone()))
            }
            Expression::LiteralString(literal_string) => {
                PyTypeEval::with_default_effects(Type::new_string_literal(literal_string.clone()))
            }
            Expression::LiteralBytes(literal_bytes) => {
                PyTypeEval::with_default_effects(Type::new_bytes_literal(literal_bytes.clone()))
            }
            Expression::LiteralBoolean(literal_boolean) => {
                PyTypeEval::with_default_effects(Type::new_boolean_literal(literal_boolean.clone()))
            }
            Expression::LiteralNone => {
                PyTypeEval::with_default_effects(Type::new_literal(TypeLiteral::None))
            }
            Expression::LiteralEllipsis => {
                PyTypeEval::with_default_effects(Type::new_literal(TypeLiteral::Ellipsis))
            }
        }
    }

    pub fn evaluate_type_constraint(
        &self,
        abstract_state: &mut EvaluationState,
        type_constraint: &IncludeConstraint<Arc<Expression>>,
    ) {
        let previous_eval = abstract_state
            .evaluations
            .values
            .get(&type_constraint.right);
        let new_eval = self.evaluate_expression(abstract_state, &type_constraint.left);

        abstract_state.evaluations.values.insert(
            type_constraint.right.clone(),
            if let Some(previous_eval) = previous_eval {
                previous_eval.join(&new_eval)
            } else {
                new_eval
            },
        );
    }
}

impl GraphAnalyser for ConstraintSolver<'_> {
    type Node = ConstraintNode;
    type AbstractState = EvaluationState;
    type AnalysisState = SolverState;
    type Metadata = (usize, Instant);
    type Error = Infallible;

    fn initialise_analysis_metadata(&self) -> Result<Self::Metadata, Self::Error> {
        Ok((0, Instant::now()))
    }
    fn before_iteration(
        &self,
        metadata: &mut Self::Metadata,
        _state: &Self::AnalysisState,
        worklist: &BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        info!(
            "[{}] Iteration {} (Worklist size: {})",
            self.program_entity_node,
            metadata.0,
            worklist.len(),
        );
        Ok(())
    }
    fn after_iteration(
        &self,
        metadata: &mut Self::Metadata,
        _state: &Self::AnalysisState,
        _worklist: &BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        debug!(
            "[{}] Iteration {} done  (after {:?})",
            self.program_entity_node,
            metadata.0,
            metadata.1.elapsed()
        );
        metadata.0 += 1;
        metadata.1 = Instant::now();
        Ok(())
    }

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
            .values
            .get(node)
            .into_iter()
            .flat_map(|tos| tos.values.keys()))
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        Ok(SolverState::default())
    }

    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
    ) -> Result<Self::AbstractState, Self::Error> {
        debug!("[{}] Analysing {}", self.program_entity_node, node);

        let mut abstract_state = analysis_state.clone_abstract_state_or_default(&node);

        match &node {
            ConstraintNode::Entry => {
                for (variable, expressions) in self.specification.arguments.as_ref() {
                    let mut ty = PyTypeEval::never();

                    for expression in expressions.as_ref() {
                        ty = ty.join(&self.evaluate_expression(&mut abstract_state, expression));
                    }

                    abstract_state.defined_variables.names.insert(
                        variable.name.clone(),
                        imbl::OrdSet::unit(variable.location.clone()),
                    );
                    abstract_state
                        .evaluations
                        .insert(Arc::new(Expression::Variable(variable.clone())), ty);
                }
            }
            ConstraintNode::TypeConstraint(constraint) => {
                self.evaluate_type_constraint(&mut abstract_state, constraint)
            }
            ConstraintNode::DefinedVariableConstraint(constraint) => {
                abstract_state.defined_variables.names.insert(
                    constraint.name.clone(),
                    imbl::OrdSet::unit(constraint.location.clone()),
                );
            }
            ConstraintNode::ReturnConstraint(constraint) => {
                let return_eval = self.evaluate_expression(&abstract_state, constraint.as_ref());
                abstract_state.return_value = return_eval.value;
            }
            _ => {}
        }

        Ok(abstract_state)
    }

    fn update_abstract_state(
        &self,
        analysis_state: &Self::AnalysisState,
        from: Self::Node,
        to: Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error> {
        Ok(Some(abstract_state.clone()))
    }

    fn get_abstract_state<'a>(
        &self,
        analysis_state: &'a Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Option<&'a Self::AbstractState>, Self::Error> {
        Ok(analysis_state.evaluation_states.get(node))
    }

    fn set_abstract_state(
        &self,
        analysis_state: &mut Self::AnalysisState,
        node: Self::Node,
        abstract_state: Self::AbstractState,
    ) -> Result<(), Self::Error> {
        analysis_state
            .evaluation_states
            .insert(node, abstract_state);
        Ok(())
    }

    fn merge(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
        left: &Self::AbstractState,
        right: &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error> {
        Ok(left.join(right))
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ProgramEntitySolverState {
    pub states: LatticeMap<ProgramEntityNode, LatticeMap<QualifiedLocation, ExitEvaluationStates>>,
}

impl Lattice for ProgramEntitySolverState {
    fn includes(&self, other: &Self) -> bool {
        self.states.includes(&other.states)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            states: self.states.join(&other.states),
        }
    }
}

pub struct ProgramEntityConstraintSolver<'a> {
    pub module_node: &'a ModuleNode,
    pub graph: &'a DependentGraph<ProgramEntityNode, ProgramAnalysis>,
    pub state: &'a LatticeMap<QualifiedLocation, ExitEvaluationStates>,
}

impl<'a> ProgramEntityConstraintSolver<'a> {
    pub fn new(
        module_node: &'a ModuleNode,
        graph: &'a DependentGraph<ProgramEntityNode, ProgramAnalysis>,
        state: &'a LatticeMap<QualifiedLocation, ExitEvaluationStates>,
    ) -> Self {
        Self {
            module_node,
            graph,
            state,
        }
    }
}

impl GraphAnalyser for ProgramEntityConstraintSolver<'_> {
    type Node = ProgramEntityNode;
    type AbstractState = LatticeMap<QualifiedLocation, ExitEvaluationStates>;
    type AnalysisState = ProgramEntitySolverState;
    type Metadata = (usize, Instant);
    type Error = Infallible;

    fn initialise_analysis_metadata(&self) -> Result<Self::Metadata, Self::Error> {
        Ok((0, Instant::now()))
    }
    fn before_iteration(
        &self,
        metadata: &mut Self::Metadata,
        _state: &Self::AnalysisState,
        worklist: &BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        info!(
            "[{}] Iteration {} (Worklist size: {})",
            self.module_node,
            metadata.0,
            worklist.len()
        );
        Ok(())
    }
    fn after_iteration(
        &self,
        metadata: &mut Self::Metadata,
        _state: &Self::AnalysisState,
        _worklist: &BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        debug!(
            "[{}] Iteration {} done (after {:?})",
            self.module_node,
            metadata.0,
            metadata.1.elapsed()
        );
        metadata.0 += 1;
        metadata.1 = Instant::now();
        Ok(())
    }

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
            .values
            .get(node)
            .map(|nodes| nodes.values.iter())
            .into_iter()
            .flatten())
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        Ok(ProgramEntitySolverState::default())
    }

    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
    ) -> Result<Self::AbstractState, Self::Error> {
        debug!("[{}] Analysing {}", self.module_node, node);

        let previous_state = analysis_state
            .states
            .get(&node)
            .cloned()
            .unwrap_or_default();

        let ProgramEntityNode::Entity(entity) = &node else {
            return Ok(previous_state);
        };

        let abstract_environment = self.graph.nodes.get(&node).unwrap();

        let solver_state = analysis(&ConstraintSolver::new(
            &node,
            &abstract_environment.specification,
            &abstract_environment.constraint_graph,
            &previous_state.clone().union(self.state.clone()),
        ))?;

        Ok(previous_state.update(
            entity.location.clone(),
            ExitEvaluationStates {
                type_evaluation_state: solver_state
                    .evaluation_states
                    .get(&ConstraintNode::TypeExit)
                    .cloned()
                    .unwrap_or_default(),
                exception_evaluation_state: solver_state
                    .evaluation_states
                    .get(&ConstraintNode::ExceptionExit)
                    .cloned()
                    .unwrap_or_default(),
            },
        ))
    }

    fn update_abstract_state(
        &self,
        analysis_state: &Self::AnalysisState,
        from: Self::Node,
        to: Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error> {
        Ok(Some(abstract_state.clone()))
    }

    fn get_abstract_state<'a>(
        &self,
        analysis_state: &'a Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Option<&'a Self::AbstractState>, Self::Error> {
        Ok(analysis_state.states.get(node))
    }

    fn set_abstract_state(
        &self,
        analysis_state: &mut Self::AnalysisState,
        node: Self::Node,
        abstract_state: Self::AbstractState,
    ) -> Result<(), Self::Error> {
        analysis_state.states.insert(node, abstract_state);
        Ok(())
    }

    fn merge(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
        left: &Self::AbstractState,
        right: &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error> {
        Ok(left.join(right))
    }
}

#[derive(Debug, Default, Clone)]
pub struct ModuleSolverState {
    pub solver_states: LatticeMap<ModuleNode, LatticeMap<QualifiedLocation, ExitEvaluationStates>>,
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
    type AbstractState = LatticeMap<QualifiedLocation, ExitEvaluationStates>;
    type AnalysisState = ModuleSolverState;
    type Metadata = (usize, Instant);
    type Error = Infallible;

    fn initialise_analysis_metadata(&self) -> Result<Self::Metadata, Self::Error> {
        Ok((0, Instant::now()))
    }
    fn before_iteration(
        &self,
        metadata: &mut Self::Metadata,
        _state: &Self::AnalysisState,
        worklist: &BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        info!(
            "Iteration {} (Worklist size: {})",
            metadata.0,
            worklist.len()
        );
        Ok(())
    }
    fn after_iteration(
        &self,
        metadata: &mut Self::Metadata,
        _state: &Self::AnalysisState,
        _worklist: &BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        debug!(
            "Iteration {} done (after {:?})",
            metadata.0,
            metadata.1.elapsed()
        );
        metadata.0 += 1;
        metadata.1 = Instant::now();
        Ok(())
    }

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
            .values
            .get(node)
            .map(|nodes| nodes.values.iter())
            .into_iter()
            .flatten())
    }

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error> {
        Ok(ModuleSolverState::default())
    }

    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
    ) -> Result<Self::AbstractState, Self::Error> {
        debug!("Analysing {}", node);

        let mut previous_state = analysis_state
            .solver_states
            .get(&node)
            .cloned()
            .unwrap_or_default();

        if let Some(dependent_graph) = self.graph.nodes.get(&node) {
            previous_state.extend(
                analysis(&ProgramEntityConstraintSolver::new(
                    &node,
                    dependent_graph,
                    &previous_state,
                ))?
                .states[&ProgramEntityNode::Exit]
                    .values
                    .clone(),
            );
        }

        Ok(previous_state)
    }

    fn update_abstract_state(
        &self,
        analysis_state: &Self::AnalysisState,
        from: Self::Node,
        to: Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error> {
        Ok(Some(abstract_state.clone()))
    }

    fn get_abstract_state<'a>(
        &self,
        analysis_state: &'a Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Option<&'a Self::AbstractState>, Self::Error> {
        Ok(analysis_state.solver_states.get(node))
    }

    fn set_abstract_state(
        &self,
        analysis_state: &mut Self::AnalysisState,
        node: Self::Node,
        abstract_state: Self::AbstractState,
    ) -> Result<(), Self::Error> {
        analysis_state.solver_states.insert(node, abstract_state);
        Ok(())
    }

    fn merge(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
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
    use crate::constraints::{
        CfgImporter, ConstraintsBuilder, ExpressionVariable, ModuleName, ProgramEntity,
        ProgramEntityKind, QualifiedLocation, analyse_program,
    };
    use apy::v1::QualifiedName;
    use apygen_analysis::analysis;
    use apygen_analysis::cfg::{Cfg, ProgramPoint};
    use indoc::indoc;
    use rstest::rstest;
    use std::collections::{HashMap, HashSet};

    fn init_logger() {
        let _ = env_logger::builder().is_test(true).try_init();
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
        a@{module[4:4]} = 42
        a@{module[6:4]} = 67
        b@{module[8:0]} = Union[42, 67]
        x@{module[1:0]} = True
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
        a@{module[1:0]} = 0
        a@{module[4:4]} = Any
        b@{module[6:0]} = Any
        "##},  // TODO: fix this when operations are implemented
    )]
    fn test_constraints_solving(#[case] source: &str, #[case] expected_types: &str) {
        init_logger();

        let cfg = Cfg::parse(source).expect("Should build CFG");

        let entity = ProgramEntity::new(
            QualifiedLocation::from(Arc::new(QualifiedName::parse("module"))),
            ProgramPoint::Entry,
            ProgramEntityKind::Module,
        );

        let constraints_builder = ConstraintsBuilder::new(&cfg, &entity, None);

        let analysis_state = analysis(&constraints_builder).expect("Should build constraints");

        let exit_state = &analysis_state.abstract_states[&ProgramPoint::Exit];

        let program_entity_node = ProgramEntityNode::Entity(entity);

        let specification = AbstractEnvironmentSpecification::default();

        let state = LatticeMap::default();

        let solver = ConstraintSolver::new(
            &program_entity_node,
            &specification,
            &exit_state.constraint_graph,
            &state,
        );

        let types = analysis(&solver).expect("analysis should work");

        let actual_types: String = types.evaluation_states[&ConstraintNode::TypeExit]
            .variables()
            .map(|(expression_variable, ty)| format!("{} = {}\n", expression_variable.clone(), ty))
            .collect();

        assert_eq!(expected_types, actual_types, "{actual_types}");
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
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a: int, b):
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        builtins:
            int@{builtins[1:6]} = class(builtins[1:6])
            #return = Never
        builtins[1:6]:
            #return = Never
        module:
            add_two@{module[1:4]} = function(module[1:4])
            result@{module[4:0]} = Any
            #return = Never
        module[1:4]:
            a@{module[1:12]} = @class(builtins[1:6])
            b@{module[1:20]} = Never
            #return = Never
        "##},
    )]
    fn test_program_constraints_solving(#[case] source: &str, #[case] expected_types: &str) {
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

        let state = analysis(&solver)
            .expect("analysis should work")
            .solver_states[&ModuleNode::Exit]
            .clone();

        let mut actual_types = String::new();
        for (node, abstract_state) in state.as_ref() {
            actual_types.push_str(&format!("{}:\n", node));
            for (variable, ty) in abstract_state.type_evaluation_state.variables() {
                actual_types.push_str(&format!("    {} = {}\n", variable, ty));
            }
            actual_types.push_str(&format!(
                "    #return = {}\n",
                abstract_state.type_evaluation_state.return_value
            ));
        }

        assert_eq!(expected_types, actual_types, "{actual_types}");
    }
}
