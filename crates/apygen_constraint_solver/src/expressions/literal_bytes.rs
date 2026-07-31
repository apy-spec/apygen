use crate::EvaluationState;
use crate::analysis::abstract_state::AbstractState;
use crate::constraint_graph::expressions::{BinaryOperator, UnaryOperator};
use crate::expressions::PyTypeEval;
use crate::identifiers::Namespace;
use crate::inference::{Exception, Sourced, Type};
use crate::primitives::ToPrimitive;
use crate::primitives::literals::{LiteralBool, LiteralBytes, LiteralInt};
use std::sync::Arc;

pub fn as_boolean(literal_bytes: &LiteralBytes) -> bool {
    !literal_bytes.value.is_empty()
}

pub fn call_dunder_bool(literal_bytes: &LiteralBytes) -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: as_boolean(literal_bytes),
    })
}

pub fn call_not(literal_bytes: &LiteralBytes) -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: !as_boolean(literal_bytes),
    })
}

pub fn call_unary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    literal_bytes: &LiteralBytes,
    operator: UnaryOperator,
) -> PyTypeEval<S> {
    match operator {
        UnaryOperator::Invert | UnaryOperator::UAdd | UnaryOperator::USub => {
            PyTypeEval::raise(Exception::any()) // TODO: fix
        }
        UnaryOperator::Not => {
            PyTypeEval::with_default_effects(Sourced::inferred(call_not(literal_bytes)))
        }
    }
}

pub fn call_binary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    left: &LiteralBytes,
    operator: BinaryOperator,
    right: &LiteralBytes,
) -> PyTypeEval<S> {
    PyTypeEval::with_default_effects(match operator {
        BinaryOperator::Add => Sourced::inferred(Type::new_bytes_literal(LiteralBytes {
            value: Arc::new(
                left.value
                    .iter()
                    .chain(right.value.iter())
                    .cloned()
                    .collect(),
            ),
        })),
        _ => return PyTypeEval::raise(Exception::any()), // TODO: fix,
    })
}

pub fn repeat_bytes<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    bytes: &LiteralBytes,
    repetitions: &LiteralInt,
) -> PyTypeEval<S> {
    if let Some(repetitions) = repetitions.value.to_usize() {
        PyTypeEval::with_default_effects(Sourced::inferred(Type::new_bytes_literal(LiteralBytes {
            value: Arc::new(Vec::from_iter(
                (0..repetitions).flat_map(|_| bytes.value.iter().cloned()),
            )),
        })))
    } else {
        PyTypeEval::unknown()
    }
}
