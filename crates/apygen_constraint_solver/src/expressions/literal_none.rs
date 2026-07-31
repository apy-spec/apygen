use crate::analysis::abstract_state::AbstractState;
use crate::identifiers::Namespace;
use crate::constraint_graph::expressions::UnaryOperator;
use crate::EvaluationState;
use crate::expressions::PyTypeEval;
use crate::inference::{Exception, Sourced, Type};
use crate::primitives::literals::LiteralBool;

pub fn as_boolean() -> bool {
    false
}

pub fn call_dunder_bool() -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: as_boolean(),
    })
}

pub fn call_not() -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: !as_boolean(),
    })
}

pub fn call_unary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(operator: UnaryOperator) -> PyTypeEval<S> {
    match operator {
        UnaryOperator::Invert | UnaryOperator::UAdd | UnaryOperator::USub => {
            PyTypeEval::raise(Exception::any()) // TODO: fix
        }
        UnaryOperator::Not => PyTypeEval::with_default_effects(Sourced::inferred(call_not())),
    }
}
