use crate::abstract_environment::{LiteralBigInteger, LiteralBoolean, Type, TypeReference};
use apygen_analysis::cfg::nodes;

pub fn as_boolean(literal_big_integer: &LiteralBigInteger) -> bool {
    literal_big_integer.value.as_str() != "0"
}

pub fn call_dunder_bool(literal_big_integer: &LiteralBigInteger) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_big_integer),
    })
}

pub fn call_not(literal_big_integer: &LiteralBigInteger) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_big_integer),
    })
}

pub fn call_dunder_pos(literal_big_integer: &LiteralBigInteger) -> Type {
    Type::new_big_integer_literal(literal_big_integer.clone())
}

pub fn call_dunder_neg(literal_big_integer: &LiteralBigInteger) -> Type {
    Type::new_big_integer_literal(LiteralBigInteger {
        value: literal_big_integer.value.clone(),
        positive: !literal_big_integer.positive,
    })
}

pub fn call_dunder_invert() -> Type {
    Type::Reference(TypeReference::builtins("int"))
}

pub fn call_unary_op(literal_big_integer: &LiteralBigInteger, operator: nodes::UnaryOp) -> Type {
    match operator {
        nodes::UnaryOp::Invert => call_dunder_invert(),
        nodes::UnaryOp::Not => call_not(literal_big_integer),
        nodes::UnaryOp::UAdd => call_dunder_pos(literal_big_integer),
        nodes::UnaryOp::USub => call_dunder_neg(literal_big_integer),
    }
}
