use crate::abstract_environment::{Exception, LiteralBoolean, LiteralBytes, LiteralInteger, Type};
use crate::constraints::{BinaryOperator, UnaryOperator};
use crate::genkill::expressions::PyTypeEval;
use num_traits::ToPrimitive;

pub fn as_boolean(literal_bytes: &LiteralBytes) -> bool {
    !literal_bytes.value.is_empty()
}

pub fn call_dunder_bool(literal_bytes: &LiteralBytes) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_bytes),
    })
}

pub fn call_not(literal_bytes: &LiteralBytes) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_bytes),
    })
}

pub fn call_unary_op(literal_bytes: &LiteralBytes, operator: UnaryOperator) -> PyTypeEval {
    match operator {
        UnaryOperator::Invert | UnaryOperator::UAdd | UnaryOperator::USub => {
            PyTypeEval::raise(Exception::any()) // TODO: fix
        }
        UnaryOperator::Not => PyTypeEval::with_default_effects(call_not(literal_bytes)),
    }
}

pub fn call_binary_op(
    left: &LiteralBytes,
    operator: BinaryOperator,
    right: &LiteralBytes,
) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
        BinaryOperator::Add => Type::new_bytes_literal(LiteralBytes {
            value: left
                .value
                .iter()
                .chain(right.value.iter())
                .cloned()
                .collect(),
        }),
        _ => return PyTypeEval::raise(Exception::any()), // TODO: fix,
    })
}

pub fn repeat_bytes(bytes: &LiteralBytes, repetitions: &LiteralInteger) -> PyTypeEval {
    if let Some(repetitions) = repetitions.to_usize() {
        PyTypeEval::with_default_effects(Type::new_bytes_literal(LiteralBytes {
            value: imbl::Vector::from_iter(
                (0..repetitions).flat_map(|_| bytes.value.iter().cloned()),
            ),
        }))
    } else {
        PyTypeEval::unknown()
    }
}
