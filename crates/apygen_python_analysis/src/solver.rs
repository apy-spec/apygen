use crate::abstract_environment::{Completeness, RaisedExceptions, Type, TypeLiteral};
use crate::constraints::{
    ConstraintGraph, ConstraintNode, DependentGraph, Expression, ExpressionBinary,
    ExpressionVariable, IncludeConstraint, LatticeMap, ModuleNode,
    ProgramEntityAbstractEnvironment, ProgramEntityNode, QualifiedLocation, VariableName,
};
use crate::genkill::expressions::{PyEffects, PyTypeEval, type_literal};
use crate::is_type_unreachable;
use crate::{pytype_consume_or_return, pytype_return_unreachable};
use apygen_analysis::lattice::Lattice;
use apygen_analysis::{GraphAnalyser, analysis};
use std::convert::Infallible;
use std::sync::Arc;

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
    pub raised_exceptions: RaisedExceptions,
    pub defined_variables: DefinedVariables,
}

impl Lattice for EvaluationState {
    fn includes(&self, other: &Self) -> bool {
        self.evaluations.includes(&other.evaluations)
            && self.raised_exceptions.includes(&other.raised_exceptions)
            && self.defined_variables.includes(&other.defined_variables)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            evaluations: self.evaluations.join(&other.evaluations),
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

pub struct ConstraintSolver<'a> {
    pub graph: &'a ConstraintGraph,
}

impl<'a> ConstraintSolver<'a> {
    pub fn new(graph: &'a ConstraintGraph) -> Self {
        Self { graph }
    }

    pub fn evaluate_expression_binary(
        &self,
        abstract_state: &EvaluationState,
        type_expression: &ExpressionBinary,
    ) -> PyTypeEval {
        let mut effects = PyEffects::new();

        let left_ty = pytype_consume_or_return!(
            effects,
            self.evaluate_type_expression(abstract_state, &type_expression.left)
        );
        let right_ty = pytype_consume_or_return!(
            effects,
            self.evaluate_type_expression(abstract_state, &type_expression.right)
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

    pub fn evaluate_type_expression(
        &self,
        abstract_state: &EvaluationState,
        type_expression: &Expression,
    ) -> PyTypeEval {
        if let Some(eval) = abstract_state.evaluations.values.get(type_expression) {
            return eval.clone();
        }

        match type_expression {
            Expression::Variable(_) => PyTypeEval::new(
                Type::Never,
                PyEffects::new().with_completeness(Completeness::Partial),
            ),
            Expression::Override(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Function(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Import(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Attribute(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Subscript(_) => PyTypeEval::with_default_effects(Type::Never),
            Expression::Call(_) => PyTypeEval::with_default_effects(Type::Never),
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
        type_constraint: &IncludeConstraint<Expression>,
    ) {
        let previous_eval = abstract_state
            .evaluations
            .values
            .get(&type_constraint.right);
        let new_eval = self.evaluate_type_expression(abstract_state, &type_constraint.left);

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
        let mut abstract_state = analysis_state.clone_abstract_state_or_default(&node);

        match &node {
            ConstraintNode::TypeConstraint(constraint) => {
                self.evaluate_type_constraint(&mut abstract_state, constraint)
            }
            ConstraintNode::DefinedVariableConstraint(constraint) => {
                abstract_state.defined_variables.names.insert(
                    constraint.name.clone(),
                    imbl::OrdSet::unit(constraint.location.clone()),
                );
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
pub struct ProgramEntityAbstractState {
    pub variable_types: LatticeMap<ExpressionVariable, Type>,
    pub exceptions: RaisedExceptions,
}

impl Lattice for ProgramEntityAbstractState {
    fn includes(&self, other: &Self) -> bool {
        self.variable_types.includes(&other.variable_types)
            && self.exceptions.includes(&other.exceptions)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            variable_types: self.variable_types.join(&other.variable_types),
            exceptions: self.exceptions.join(&other.exceptions),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ProgramEntitySolverState {
    pub states:
        LatticeMap<ProgramEntityNode, LatticeMap<ProgramEntityNode, ProgramEntityAbstractState>>,
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
    pub graph: &'a DependentGraph<ProgramEntityNode, ProgramEntityAbstractEnvironment>,
}

impl<'a> ProgramEntityConstraintSolver<'a> {
    pub fn new(
        graph: &'a DependentGraph<ProgramEntityNode, ProgramEntityAbstractEnvironment>,
    ) -> Self {
        Self { graph }
    }
}

impl GraphAnalyser for ProgramEntityConstraintSolver<'_> {
    type Node = ProgramEntityNode;
    type AbstractState = LatticeMap<ProgramEntityNode, ProgramEntityAbstractState>;
    type AnalysisState = ProgramEntitySolverState;
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
        let previous_state = analysis_state
            .states
            .get(&node)
            .cloned()
            .unwrap_or_default();

        if let Some(abstract_environment) = self.graph.nodes.get(&node) {
            let solver_state = analysis(&ConstraintSolver::new(
                &abstract_environment.constraint_graph,
            ))?;
            let type_exit = solver_state
                .evaluation_states
                .get(&ConstraintNode::TypeExit);
            let type_exceptions = solver_state
                .evaluation_states
                .get(&ConstraintNode::ExceptionExit);

            let variable_types: LatticeMap<_, _> = type_exit
                .unwrap()
                .defined_variables
                .names
                .iter()
                .map(|(variable, locations)| {
                    locations.iter().map(|location| {
                        let expression_variable =
                            ExpressionVariable::new(variable.clone(), location.clone());

                        (
                            expression_variable.clone(),
                            type_exit
                                .and_then(|type_exit| {
                                    type_exit
                                        .evaluations
                                        .get(&Expression::Variable(expression_variable))
                                })
                                .map(|eval| eval.value.clone())
                                .unwrap_or(Type::Never),
                        )
                    })
                })
                .flatten()
                .collect();
            let exceptions = type_exceptions
                .map(|type_exceptions| type_exceptions.raised_exceptions.clone())
                .unwrap_or(RaisedExceptions::default());

            Ok(previous_state.update_join(
                node,
                ProgramEntityAbstractState {
                    variable_types,
                    exceptions,
                },
            ))
        } else {
            Ok(previous_state)
        }
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
    pub solver_states: LatticeMap<
        ModuleNode,
        LatticeMap<ModuleNode, LatticeMap<ProgramEntityNode, ProgramEntityAbstractState>>,
    >,
}

pub struct ModuleConstraintSolver<'a> {
    pub graph: &'a DependentGraph<
        ModuleNode,
        DependentGraph<ProgramEntityNode, ProgramEntityAbstractEnvironment>,
    >,
}

impl<'a> ModuleConstraintSolver<'a> {
    pub fn new(
        graph: &'a DependentGraph<
            ModuleNode,
            DependentGraph<ProgramEntityNode, ProgramEntityAbstractEnvironment>,
        >,
    ) -> Self {
        Self { graph }
    }
}

impl GraphAnalyser for ModuleConstraintSolver<'_> {
    type Node = ModuleNode;
    type AbstractState =
        LatticeMap<ModuleNode, LatticeMap<ProgramEntityNode, ProgramEntityAbstractState>>;
    type AnalysisState = ModuleSolverState;
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
        let previous_state = analysis_state
            .solver_states
            .get(&node)
            .cloned()
            .unwrap_or_default();

        if let Some(dependent_graph) = self.graph.nodes.get(&node) {
            Ok(previous_state.update_join(
                node,
                analysis(&ProgramEntityConstraintSolver::new(dependent_graph))?.states
                    [&ProgramEntityNode::Exit]
                    .clone(),
            ))
        } else {
            Ok(previous_state)
        }
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
        a@{module[4:4]} = builtins.Literal[42]
        a@{module[6:4]} = builtins.Literal[67]
        b@{module[8:0]} = Union[builtins.Literal[42], builtins.Literal[67]]
        x@{module[1:0]} = builtins.Literal[true]
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
        a@{module[1:0]} = builtins.Literal[0]
        a@{module[4:4]} = Any
        b@{module[6:0]} = Any
        "##},  // TODO: fix this when operations are implemented
    )]
    fn test_constraints_solving(#[case] source: &str, #[case] expected_types: &str) {
        let cfg = Cfg::parse(source).expect("Should build CFG");

        let entity = ProgramEntity::new(
            QualifiedLocation::from(Arc::new(QualifiedName::parse("module"))),
            ProgramPoint::Entry,
            ProgramEntityKind::Module,
        );

        let constraints_builder = ConstraintsBuilder::new(&cfg, &entity, None);

        let analysis_state = analysis(&constraints_builder).expect("Should build constraints");

        let exit_state = &analysis_state.abstract_states[&ProgramPoint::Exit];

        let solver = ConstraintSolver::new(&exit_state.constraint_graph);

        let types = analysis(&solver).expect("analysis should work");

        let type_exit_evaluations = &types.evaluation_states[&ConstraintNode::TypeExit];

        let actual_types: String = type_exit_evaluations
            .defined_variables
            .names
            .iter()
            .map(|(variable, locations)| {
                locations.iter().map(|location| {
                    let expression_variable =
                        ExpressionVariable::new(variable.clone(), location.clone());
                    format!(
                        "{} = {}\n",
                        expression_variable.clone(),
                        type_exit_evaluations.evaluations.values
                            [&Expression::Variable(expression_variable)]
                            .value
                    )
                })
            })
            .flatten()
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

    #[rstest]
    #[case::simple_function_definition(
        indoc! {r##"
        def add_two(a, b):
            return a + b

        result = add_two(42, 67)
        "##},
        indoc! {r##"
        Module(builtins):
            Entity(builtins):
        Module(module):
            Entity(module):
                add_two@{module[1:4]} = Never
                result@{module[4:0]} = Never
        "##},
    )]
    fn test_program_constraints_solving(#[case] source: &str, #[case] expected_types: &str) {
        let module_name = Arc::new(QualifiedName::parse("module"));
        let cfg = Cfg::parse(source).expect("Should build CFG");

        let cfg_importer = TestCfgImporter {
            modules: HashMap::from_iter([
                (module_name.clone(), cfg),
                (
                    Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                    Cfg::parse("").expect("Should build CFG"),
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
        for (module_node, graph) in state.as_ref() {
            actual_types.push_str(&format!("{}:\n", module_node));
            for (node, abstract_state) in graph.as_ref() {
                actual_types.push_str(&format!("    {}:\n", node));
                for (variable, ty) in abstract_state.variable_types.as_ref() {
                    actual_types.push_str(&format!("        {} = {}\n", variable, ty));
                }
            }
        }

        assert_eq!(expected_types, actual_types, "{actual_types}");
    }
}
