use crate::abstract_environment::{LiteralBoolean, LiteralInteger, Type};
use apygen_analysis::cfg::nodes;

pub fn as_boolean(literal_boolean: &LiteralBoolean) -> bool {
    literal_boolean.value
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
    Type::new_integer_literal(LiteralInteger {
        value: if literal_boolean.value { 1 } else { 0 },
    })
}

pub fn call_dunder_neg(literal_boolean: &LiteralBoolean) -> Type {
    Type::new_integer_literal(LiteralInteger {
        value: if literal_boolean.value { -1 } else { 0 },
    })
}

pub fn call_dunder_invert(literal_boolean: &LiteralBoolean) -> Type {
    Type::new_integer_literal(LiteralInteger {
        value: if literal_boolean.value { -2 } else { -1 },
    })
}

pub fn call_unary_op(literal_boolean: &LiteralBoolean, operator: nodes::UnaryOp) -> Type {
    match operator {
        nodes::UnaryOp::Invert => call_dunder_invert(literal_boolean),
        nodes::UnaryOp::Not => call_not(literal_boolean),
        nodes::UnaryOp::UAdd => call_dunder_pos(literal_boolean),
        nodes::UnaryOp::USub => call_dunder_neg(literal_boolean),
    }
}
