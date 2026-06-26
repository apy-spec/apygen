use crate::abstract_environment::{LiteralBoolean, LiteralInteger, Type};
use crate::constraints::{BinaryOperator, UnaryOperator};
use crate::genkill::expressions;
use crate::genkill::expressions::PyTypeEval;

pub fn as_integer(literal_boolean: &LiteralBoolean) -> i64 {
    if literal_boolean.value { 1 } else { 0 }
}

pub fn as_boolean(literal_boolean: &LiteralBoolean) -> bool {
    literal_boolean.value
}

pub fn call_dunder_int(literal_boolean: &LiteralBoolean) -> Type {
    Type::new_integer_literal(LiteralInteger::Int(as_integer(literal_boolean)))
}

pub fn call_dunder_bool(literal_boolean: &LiteralBoolean) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_boolean),
    })
}

pub fn call_not(literal_boolean: &LiteralBoolean) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_boolean),
    })
}

pub fn call_dunder_pos(literal_boolean: &LiteralBoolean) -> Type {
    Type::new_integer_literal(LiteralInteger::Int(as_integer(literal_boolean)))
}

pub fn call_dunder_neg(literal_boolean: &LiteralBoolean) -> Type {
    Type::new_integer_literal(LiteralInteger::Int(-as_integer(literal_boolean)))
}

pub fn call_dunder_invert(literal_boolean: &LiteralBoolean) -> Type {
    Type::new_integer_literal(LiteralInteger::Int(!as_integer(literal_boolean)))
}

pub fn call_unary_op(literal_boolean: &LiteralBoolean, operator: UnaryOperator) -> Type {
    match operator {
        UnaryOperator::Invert => call_dunder_invert(literal_boolean),
        UnaryOperator::Not => call_not(literal_boolean),
        UnaryOperator::UAdd => call_dunder_pos(literal_boolean),
        UnaryOperator::USub => call_dunder_neg(literal_boolean),
    }
}

pub fn call_binary_op(
    left: &LiteralBoolean,
    operator: BinaryOperator,
    right: &LiteralBoolean,
) -> PyTypeEval {
    expressions::literal_integer::call_binary_op(
        &LiteralInteger::Int(as_integer(left)),
        operator,
        &LiteralInteger::Int(as_integer(right)),
    )
}
