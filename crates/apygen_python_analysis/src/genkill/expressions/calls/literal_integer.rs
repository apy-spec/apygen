use crate::abstract_environment::{LiteralBoolean, LiteralInteger, Type};
use apygen_analysis::cfg::nodes;

pub fn as_boolean(literal_integer: &LiteralInteger) -> bool {
    literal_integer.value != 0
}

pub fn call_dunder_bool(literal_integer: &LiteralInteger) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_integer),
    })
}

pub fn call_not(literal_integer: &LiteralInteger) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_integer),
    })
}

pub fn call_dunder_pos(literal_integer: &LiteralInteger) -> Type {
    Type::new_integer_literal(LiteralInteger {
        value: literal_integer.value,
    })
}

pub fn call_dunder_neg(literal_integer: &LiteralInteger) -> Type {
    Type::new_integer_literal(LiteralInteger {
        value: -literal_integer.value,
    })
}

pub fn call_dunder_invert(literal_integer: &LiteralInteger) -> Type {
    Type::new_integer_literal(LiteralInteger {
        value: !literal_integer.value, // Equivalent of ~ in Rust is ! for integers
    })
}

pub fn call_unary_op(literal_integer: &LiteralInteger, operator: nodes::UnaryOp) -> Type {
    match operator {
        nodes::UnaryOp::Invert => call_dunder_invert(literal_integer),
        nodes::UnaryOp::Not => call_not(literal_integer),
        nodes::UnaryOp::UAdd => call_dunder_pos(literal_integer),
        nodes::UnaryOp::USub => call_dunder_neg(literal_integer),
    }
}
