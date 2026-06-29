use crate::abstract_environment::{Completeness, RaisedExceptions, Type, TypeLiteral};
use crate::constraints::{
    ConstraintGraph, ConstraintNode, ExceptionExpression, ExpressionBinary, IncludeConstraint,
    IncludeConstraintDefinition, LatticeMap, TypeExpression,
};
use crate::genkill::expressions::{PyEffects, PyTypeEval, type_literal};
use crate::is_type_unreachable;
use crate::{pytype_consume_or_return, pytype_return_unreachable};
use apygen_analysis::GraphAnalyser;
use apygen_analysis::lattice::Lattice;
use std::collections::HashMap;
use std::convert::Infallible;
use std::sync::Arc;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct EvaluationState {
    pub type_evaluations: LatticeMap<Arc<TypeExpression>, PyTypeEval>,
    pub exception_evaluations: LatticeMap<Arc<ExceptionExpression>, RaisedExceptions>,
}

impl Lattice for EvaluationState {
    fn includes(&self, other: &Self) -> bool {
        self.type_evaluations.includes(&other.type_evaluations)
            && self
                .exception_evaluations
                .includes(&other.exception_evaluations)
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            type_evaluations: self.type_evaluations.join(&other.type_evaluations),
            exception_evaluations: self
                .exception_evaluations
                .join(&other.exception_evaluations),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct SolverState {
    pub evaluation_states: HashMap<ConstraintNode, EvaluationState>,
}

impl SolverState {
    pub fn clone_abstract_state_or_default(&self, node: &ConstraintNode) -> EvaluationState {
        self.evaluation_states
            .get(node)
            .cloned()
            .unwrap_or_default()
    }
}

pub struct ConstraintSolver<'a> {
    pub graph: &'a ConstraintGraph,
}

impl ConstraintSolver<'_> {
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
        type_expression: &TypeExpression,
    ) -> PyTypeEval {
        if let Some(eval) = abstract_state.type_evaluations.values.get(type_expression) {
            return eval.clone();
        }

        match type_expression {
            TypeExpression::Variable(_) => PyTypeEval::new(
                Type::Never,
                PyEffects::new().with_completeness(Completeness::Partial),
            ),
            TypeExpression::Override(_) => PyTypeEval::with_default_effects(Type::Never),
            TypeExpression::Function(_) => PyTypeEval::with_default_effects(Type::Never),
            TypeExpression::Import(_) => PyTypeEval::with_default_effects(Type::Never),
            TypeExpression::Attribute(_) => PyTypeEval::with_default_effects(Type::Never),
            TypeExpression::Subscript(_) => PyTypeEval::with_default_effects(Type::Never),
            TypeExpression::Call(_) => PyTypeEval::with_default_effects(Type::Never),
            TypeExpression::Unary(_) => PyTypeEval::with_default_effects(Type::Never),
            TypeExpression::Binary(expression_binary) => {
                self.evaluate_expression_binary(abstract_state, expression_binary)
            }
            TypeExpression::LiteralInteger(literal_integer) => {
                PyTypeEval::with_default_effects(Type::new_integer_literal(literal_integer.clone()))
            }
            TypeExpression::LiteralFloat(literal_float) => {
                PyTypeEval::with_default_effects(Type::new_float_literal(literal_float.clone()))
            }
            TypeExpression::LiteralComplex(literal_complex) => {
                PyTypeEval::with_default_effects(Type::new_complex_literal(literal_complex.clone()))
            }
            TypeExpression::LiteralString(literal_string) => {
                PyTypeEval::with_default_effects(Type::new_string_literal(literal_string.clone()))
            }
            TypeExpression::LiteralBytes(literal_bytes) => {
                PyTypeEval::with_default_effects(Type::new_bytes_literal(literal_bytes.clone()))
            }
            TypeExpression::LiteralBoolean(literal_boolean) => {
                PyTypeEval::with_default_effects(Type::new_boolean_literal(literal_boolean.clone()))
            }
            TypeExpression::LiteralNone => {
                PyTypeEval::with_default_effects(Type::new_literal(TypeLiteral::None))
            }
            TypeExpression::LiteralEllipsis => {
                PyTypeEval::with_default_effects(Type::new_literal(TypeLiteral::Ellipsis))
            }
        }
    }

    pub fn evaluate_type_constraint(
        &self,
        abstract_state: &mut EvaluationState,
        type_constraint: &IncludeConstraintDefinition<TypeExpression>,
    ) {
        let previous_eval = abstract_state
            .type_evaluations
            .values
            .get(&type_constraint.right);
        let new_eval = self.evaluate_type_expression(abstract_state, &type_constraint.left);

        abstract_state.type_evaluations.values.insert(
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

    fn entry_node(&self) -> Result<Self::Node, Self::Error> {
        Ok(ConstraintNode::Entry)
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
            ConstraintNode::Constraint(constraint) => match constraint.as_ref() {
                IncludeConstraint::Type(constraint_type) => {
                    self.evaluate_type_constraint(&mut abstract_state, constraint_type)
                }
                IncludeConstraint::Exception(_) => {}
            },
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints::{AbstractEnvironment, AnalysisState, ConstraintsBuilder, ExpressionVariable, ModuleName};
    use apygen_analysis::analysis;
    use apygen_analysis::cfg::{Cfg, ProgramPoint};
    use apygen_analysis::namespace::Namespace;
    use indoc::indoc;
    use rstest::rstest;
    use std::sync::mpsc;

    fn generate_constraints(source: &str) -> (AnalysisState, Vec<String>) {
        let cfg = Cfg::parse(source).expect("Should build CFG");

        let (import_tx, import_rx) = mpsc::channel::<ModuleName>();

        let constraints_builder = ConstraintsBuilder::new(&cfg, &import_tx);

        let namespace = analysis(&constraints_builder).expect("constraint builder should work");

        drop(import_tx);

        let imports = import_rx
            .iter()
            .map(|module_name| module_name.join())
            .collect::<Vec<_>>();

        (namespace, imports)
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
        a@(4:4) = builtins.Literal[42]
        a@(6:4) = builtins.Literal[67]
        a@(8:4) = Union[builtins.Literal[42], builtins.Literal[67]]
        b@(8:0) = Union[builtins.Literal[42], builtins.Literal[67]]
        x@(1:0) = builtins.Literal[true]
        x@(3:3) = builtins.Literal[true]
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
        a@(1:0) = builtins.Literal[0]
        a@(3:6) = Any
        a@(4:4) = Any
        a@(6:4) = Any
        b@(6:0) = Any
        "##},  // TODO: fix this when operations are implemented
    )]
    fn test_constraints_solving(#[case] source: &str, #[case] expected_types: &str) {
        let (namespace, _) = generate_constraints(&source);

        let exit_state = &namespace.abstract_states[&ProgramPoint::Exit];

        let solver = ConstraintSolver {
            graph: &exit_state.constraint_graph,
        };

        let types = analysis(&solver).expect("analysis should work");

        let type_exit_evaluations = &types.evaluation_states[&ConstraintNode::TypeExit];

        let actual_types: String = exit_state
            .variable_locations
            .values
            .iter()
            .map(|(variable, definitions)| {
                definitions.values.iter().map(|definition| {
                    let expression_variable =
                        ExpressionVariable::new(variable.clone(), definition.clone());
                    format!(
                        "{} = {}\n",
                        expression_variable.clone(),
                        type_exit_evaluations.type_evaluations.values
                            [&TypeExpression::Variable(expression_variable)]
                            .value
                    )
                })
            })
            .flatten()
            .collect();

        assert_eq!(expected_types, actual_types, "{actual_types}");
    }
}
