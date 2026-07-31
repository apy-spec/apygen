use crate::EvaluationState;
use crate::analysis::abstract_state::AbstractState;
use crate::constraint_graph::expressions::{BinaryOperator, UnaryOperator};
use crate::expressions::PyTypeEval;
use crate::identifiers::Namespace;
use crate::inference::{Exception, Sourced, Type};
use crate::primitives::ToPrimitive;
use crate::primitives::literals::{LiteralBool, LiteralInt, LiteralStr};
use std::sync::Arc;

pub fn as_boolean(literal_string: &LiteralStr) -> bool {
    !literal_string.value.is_empty()
}

pub fn call_dunder_bool(literal_string: &LiteralStr) -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: as_boolean(literal_string),
    })
}

pub fn call_not(literal_string: &LiteralStr) -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: !as_boolean(literal_string),
    })
}

pub fn call_unary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    literal_string: &LiteralStr,
    operator: UnaryOperator,
) -> PyTypeEval<S> {
    match operator {
        UnaryOperator::Invert | UnaryOperator::UAdd | UnaryOperator::USub => {
            PyTypeEval::raise(Exception::any()) // TODO: fix
        }
        UnaryOperator::Not => {
            PyTypeEval::with_default_effects(Sourced::inferred(call_not(literal_string)))
        }
    }
}

pub fn call_binary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    left: &LiteralStr,
    operator: BinaryOperator,
    right: &LiteralStr,
) -> PyTypeEval<S> {
    PyTypeEval::with_default_effects(Sourced::inferred(match operator {
        BinaryOperator::Add => Type::new_string_literal({
            let mut value = String::new();
            value.push_str(left.value.as_str());
            value.push_str(right.value.as_str());
            LiteralStr {
                value: Arc::new(value),
            }
        }),
        _ => return PyTypeEval::raise(Exception::any()), // TODO: fix
    }))
}

pub fn repeat_string<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    string: &LiteralStr,
    repetitions: &LiteralInt,
) -> PyTypeEval<S> {
    if let Some(repetitions) = repetitions.value.to_usize() {
        PyTypeEval::with_default_effects(Sourced::inferred(Type::new_string_literal(LiteralStr {
            value: Arc::new(string.value.repeat(repetitions)),
        })))
    } else {
        PyTypeEval::unknown()
    }
}
