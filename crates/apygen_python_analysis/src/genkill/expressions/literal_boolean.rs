use crate::abstract_environment::Type;
use crate::constraints::{BinaryOperator, UnaryOperator};
use crate::genkill::expressions;
use crate::genkill::expressions::PyTypeEval;
use crate::primitives::literals::{LiteralBool, LiteralInt};

pub fn as_integer(literal_boolean: &LiteralBool) -> i64 {
    if literal_boolean.value { 1 } else { 0 }
}

pub fn as_boolean(literal_boolean: &LiteralBool) -> bool {
    literal_boolean.value
}

pub fn call_dunder_int(literal_boolean: &LiteralBool) -> Type {
    Type::new_integer_literal(LiteralInt::from(as_integer(literal_boolean)))
}

pub fn call_dunder_bool(literal_boolean: &LiteralBool) -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: as_boolean(literal_boolean),
    })
}

pub fn call_not(literal_boolean: &LiteralBool) -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: !as_boolean(literal_boolean),
    })
}

pub fn call_dunder_pos(literal_boolean: &LiteralBool) -> Type {
    Type::new_integer_literal(LiteralInt::from(as_integer(literal_boolean)))
}

pub fn call_dunder_neg(literal_boolean: &LiteralBool) -> Type {
    Type::new_integer_literal(LiteralInt::from(-as_integer(literal_boolean)))
}

pub fn call_dunder_invert(literal_boolean: &LiteralBool) -> Type {
    Type::new_integer_literal(LiteralInt::from(!as_integer(literal_boolean)))
}

pub fn call_unary_op(literal_boolean: &LiteralBool, operator: UnaryOperator) -> Type {
    match operator {
        UnaryOperator::Invert => call_dunder_invert(literal_boolean),
        UnaryOperator::Not => call_not(literal_boolean),
        UnaryOperator::UAdd => call_dunder_pos(literal_boolean),
        UnaryOperator::USub => call_dunder_neg(literal_boolean),
    }
}

pub fn call_binary_op(
    left: &LiteralBool,
    operator: BinaryOperator,
    right: &LiteralBool,
) -> PyTypeEval {
    expressions::literal_integer::call_binary_op(
        &LiteralInt::from(as_integer(left)),
        operator,
        &LiteralInt::from(as_integer(right)),
    )
}
