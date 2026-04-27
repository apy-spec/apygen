use crate::abstract_environment::{
    BUILTINS_MODULE, Exception, LiteralBoolean, LiteralInteger, Type, TypeReference,
};
use crate::genkill::expressions::GenExprResult;
use apy::v1::QualifiedName;
use apygen_analysis::cfg::nodes;
use std::sync::Arc;

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

pub fn call_binary_op(
    left: &LiteralInteger,
    operator: nodes::Operator,
    right: &LiteralInteger,
) -> GenExprResult<Type> {
    GenExprResult::new_total_pure_non_raising(match operator {
        nodes::Operator::Add => Type::new_integer_literal(LiteralInteger {
            value: left.value + right.value,
        }),
        nodes::Operator::Sub => Type::new_integer_literal(LiteralInteger {
            value: left.value - right.value,
        }),
        nodes::Operator::Mult => Type::new_integer_literal(LiteralInteger {
            value: left.value * right.value,
        }),
        nodes::Operator::MatMult => return GenExprResult::raise(Exception::type_error()),
        nodes::Operator::Div => {
            if right.value == 0 {
                return GenExprResult::raise(Exception::from_type(Type::Reference(
                    TypeReference::new(
                        Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                        QualifiedName::parse("ZeroDivisionError"),
                    ),
                )));
            } else {
                Type::new_integer_literal(LiteralInteger {
                    value: left.value / right.value,
                })
            }
        }
        nodes::Operator::Mod => {
            if right.value == 0 {
                return GenExprResult::raise(Exception::from_type(Type::Reference(
                    TypeReference::new(
                        Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                        QualifiedName::parse("ZeroDivisionError"),
                    ),
                )));
            } else {
                Type::new_integer_literal(LiteralInteger {
                    value: left.value % right.value,
                })
            }
        }
        nodes::Operator::Pow => {
            if let Ok(value) = u32::try_from(right.value) {
                Type::new_integer_literal(LiteralInteger {
                    value: left.value.pow(value),
                })
            } else {
                Type::Reference(TypeReference::new(
                    Arc::new(QualifiedName::parse(BUILTINS_MODULE)),
                    QualifiedName::parse("int"),
                ))
            }
        }
        nodes::Operator::LShift => Type::new_integer_literal(LiteralInteger {
            value: left.value << right.value,
        }),
        nodes::Operator::RShift => Type::new_integer_literal(LiteralInteger {
            value: left.value >> right.value,
        }),
        nodes::Operator::BitOr => Type::new_integer_literal(LiteralInteger {
            value: left.value | right.value,
        }),
        nodes::Operator::BitXor => Type::new_integer_literal(LiteralInteger {
            value: left.value ^ right.value,
        }),
        nodes::Operator::BitAnd => Type::new_integer_literal(LiteralInteger {
            value: left.value & right.value,
        }),
        nodes::Operator::FloorDiv => Type::new_integer_literal(LiteralInteger {
            value: left.value / right.value,
        }),
    })
}
