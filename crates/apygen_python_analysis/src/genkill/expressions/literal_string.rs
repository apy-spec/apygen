use crate::abstract_environment::{Exception, Type};
use crate::constraints::{BinaryOperator, UnaryOperator};
use crate::genkill::expressions::PyTypeEval;
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

pub fn call_unary_op(literal_string: &LiteralStr, operator: UnaryOperator) -> PyTypeEval {
    match operator {
        UnaryOperator::Invert | UnaryOperator::UAdd | UnaryOperator::USub => {
            PyTypeEval::raise(Exception::any()) // TODO: fix
        }
        UnaryOperator::Not => PyTypeEval::with_default_effects(call_not(literal_string)),
    }
}

pub fn call_binary_op(
    left: &LiteralStr,
    operator: BinaryOperator,
    right: &LiteralStr,
) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
        BinaryOperator::Add => Type::new_string_literal({
            let mut value = String::new();
            value.push_str(left.value.as_str());
            value.push_str(right.value.as_str());
            LiteralStr {
                value: Arc::new(value),
            }
        }),
        _ => return PyTypeEval::raise(Exception::any()), // TODO: fix
    })
}

pub fn repeat_string(string: &LiteralStr, repetitions: &LiteralInt) -> PyTypeEval {
    if let Some(repetitions) = repetitions.value.to_usize() {
        PyTypeEval::with_default_effects(Type::new_string_literal(LiteralStr {
            value: Arc::new(string.value.repeat(repetitions)),
        }))
    } else {
        PyTypeEval::unknown()
    }
}
