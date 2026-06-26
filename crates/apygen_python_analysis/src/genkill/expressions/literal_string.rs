use crate::abstract_environment::{Exception, ExceptionOrigin, LiteralBoolean, LiteralInteger, LiteralString, Type};
use crate::genkill::expressions::PyTypeEval;
use num_traits::ToPrimitive;
use std::sync::Arc;
use crate::constraints::{BinaryOperator, UnaryOperator};

pub fn as_boolean(literal_string: &LiteralString) -> bool {
    !literal_string.value.is_empty()
}

pub fn call_dunder_bool(literal_string: &LiteralString) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_string),
    })
}

pub fn call_not(literal_string: &LiteralString) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_string),
    })
}

pub fn call_unary_op(literal_string: &LiteralString, operator: UnaryOperator) -> PyTypeEval {
    match operator {
        UnaryOperator::Invert | UnaryOperator::UAdd | UnaryOperator::USub => {
            PyTypeEval::raise(Exception::type_error(ExceptionOrigin::Unknown))
        }
        UnaryOperator::Not => PyTypeEval::with_default_effects(call_not(literal_string)),
    }
}

pub fn call_binary_op(
    left: &LiteralString,
    operator: BinaryOperator,
    right: &LiteralString,
) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
        BinaryOperator::Add => Type::new_string_literal({
            let mut value = String::new();
            value.push_str(left.value.as_str());
            value.push_str(right.value.as_str());
            LiteralString {
                value: Arc::new(value),
            }
        }),
        _ => return PyTypeEval::raise(Exception::type_error(ExceptionOrigin::Unknown)),
    })
}

pub fn repeat_string(string: &LiteralString, repetitions: &LiteralInteger) -> PyTypeEval {
    if let Some(repetitions) = repetitions.to_usize() {
        PyTypeEval::with_default_effects(Type::new_string_literal(LiteralString {
            value: Arc::new(string.value.repeat(repetitions)),
        }))
    } else {
        PyTypeEval::unknown()
    }
}
