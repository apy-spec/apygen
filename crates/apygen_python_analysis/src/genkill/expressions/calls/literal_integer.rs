use crate::abstract_environment::{
    Exception, LiteralBigInteger, LiteralBoolean, LiteralInteger, Type, TypeReference,
};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;
use num_bigint::BigInt;

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
        nodes::Operator::Add => {
            if let Some(addition) = left.value.checked_add(right.value) {
                Type::new_integer_literal(LiteralInteger { value: addition })
            } else {
                Type::new_big_integer_literal(LiteralBigInteger {
                    value: BigInt::from(left.value) + BigInt::from(right.value),
                })
            }
        }
        nodes::Operator::Sub => {
            if let Some(subtraction) = left.value.checked_sub(right.value) {
                Type::new_integer_literal(LiteralInteger { value: subtraction })
            } else {
                Type::new_big_integer_literal(LiteralBigInteger {
                    value: BigInt::from(left.value) - BigInt::from(right.value),
                })
            }
        }
        nodes::Operator::Mult => {
            if let Some(multiplication) = left.value.checked_mul(right.value) {
                Type::new_integer_literal(LiteralInteger {
                    value: multiplication,
                })
            } else {
                Type::new_big_integer_literal(LiteralBigInteger {
                    value: BigInt::from(left.value) * BigInt::from(right.value),
                })
            }
        }
        nodes::Operator::MatMult => return GenExprResult::raise(Exception::type_error()),
        nodes::Operator::Div | nodes::Operator::FloorDiv => {
            if right.value == 0 {
                return GenExprResult::raise(Exception::from_type(Type::Reference(
                    TypeReference::builtins("ZeroDivisionError"),
                )));
            } else {
                if let Some(division) = left.value.checked_div(right.value) {
                    Type::new_integer_literal(LiteralInteger { value: division })
                } else {
                    Type::new_big_integer_literal(LiteralBigInteger {
                        value: BigInt::from(left.value) / BigInt::from(right.value),
                    })
                }
            }
        }
        nodes::Operator::Mod => {
            if right.value == 0 {
                return GenExprResult::raise(Exception::from_type(Type::Reference(
                    TypeReference::builtins("ZeroDivisionError"),
                )));
            } else {
                if let Some(division) = left.value.checked_rem(right.value) {
                    Type::new_integer_literal(LiteralInteger { value: division })
                } else {
                    Type::new_big_integer_literal(LiteralBigInteger {
                        value: BigInt::from(left.value) % BigInt::from(right.value),
                    })
                }
            }
        }
        nodes::Operator::Pow => {
            if let Ok(value) = u32::try_from(right.value) {
                if let Some(power) = left.value.checked_pow(value) {
                    Type::new_integer_literal(LiteralInteger { value: power })
                } else {
                    Type::new_big_integer_literal(LiteralBigInteger {
                        value: BigInt::from(left.value).pow(value),
                    })
                }
            } else {
                return GenExprResult::raise(Exception::from_type(Type::Any));
            }
        }
        nodes::Operator::LShift => {
            if let Ok(value) = u32::try_from(right.value) {
                if let Some(shift_left) = left.value.checked_shl(value) {
                    Type::new_integer_literal(LiteralInteger { value: shift_left })
                } else {
                    Type::new_big_integer_literal(LiteralBigInteger {
                        value: BigInt::from(left.value) << value,
                    })
                }
            } else {
                return GenExprResult::raise(Exception::from_type(Type::Any));
            }
        }
        nodes::Operator::RShift => {
            if let Ok(value) = u32::try_from(right.value) {
                if let Some(shift_right) = left.value.checked_shr(value) {
                    Type::new_integer_literal(LiteralInteger { value: shift_right })
                } else {
                    Type::new_big_integer_literal(LiteralBigInteger {
                        value: BigInt::from(left.value) >> value,
                    })
                }
            } else {
                return GenExprResult::raise(Exception::from_type(Type::Any));
            }
        }
        nodes::Operator::BitOr => Type::new_integer_literal(LiteralInteger {
            value: left.value | right.value,
        }),
        nodes::Operator::BitXor => Type::new_integer_literal(LiteralInteger {
            value: left.value ^ right.value,
        }),
        nodes::Operator::BitAnd => Type::new_integer_literal(LiteralInteger {
            value: left.value & right.value,
        }),
    })
}
