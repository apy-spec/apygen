use crate::abstract_environment::{
    Exception, LiteralBigInteger, LiteralBoolean, Type, TypeReference,
};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;
use num_bigint::BigInt;

pub fn as_boolean(literal_big_integer: &LiteralBigInteger) -> bool {
    literal_big_integer.value != BigInt::ZERO
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
        value: -literal_big_integer.value.clone(),
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

pub fn call_binary_op(
    left: &LiteralBigInteger,
    operator: nodes::Operator,
    right: &LiteralBigInteger,
) -> GenExprResult<Type> {
    GenExprResult::new_total_pure_non_raising(match operator {
        nodes::Operator::Add => Type::new_big_integer_literal(LiteralBigInteger {
            value: &left.value + &right.value,
        }),
        nodes::Operator::Sub => Type::new_big_integer_literal(LiteralBigInteger {
            value: &left.value - &right.value,
        }),
        nodes::Operator::Mult => Type::new_big_integer_literal(LiteralBigInteger {
            value: &left.value * &right.value,
        }),
        nodes::Operator::Pow => {
            let Ok(value) = u32::try_from(&right.value) else {
                return GenExprResult::unknown();
            };

            Type::new_big_integer_literal(LiteralBigInteger {
                value: left.value.pow(value),
            })
        }
        nodes::Operator::Div => {
            if right.value == BigInt::ZERO {
                return GenExprResult::raise(Exception::from_type(Type::Reference(
                    TypeReference::builtins("ZeroDivisionError"),
                )));
            }

            Type::new_big_integer_literal(LiteralBigInteger {
                value: &left.value / &right.value,
            })
        }
        nodes::Operator::FloorDiv => Type::new_big_integer_literal(LiteralBigInteger {
            value: &left.value / &right.value,
        }),
        nodes::Operator::Mod => {
            if right.value == BigInt::ZERO {
                return GenExprResult::raise(Exception::from_type(Type::Reference(
                    TypeReference::builtins("ZeroDivisionError"),
                )));
            }

            Type::new_big_integer_literal(LiteralBigInteger {
                value: &left.value % &right.value,
            })
        }
        nodes::Operator::LShift => {
            let Ok(value) = u32::try_from(&right.value) else {
                return GenExprResult::unknown();
            };

            Type::new_big_integer_literal(LiteralBigInteger {
                value: &left.value << value,
            })
        }
        nodes::Operator::RShift => {
            let Ok(value) = u32::try_from(&right.value) else {
                return GenExprResult::unknown();
            };

            Type::new_big_integer_literal(LiteralBigInteger {
                value: &left.value >> value,
            })
        }
        nodes::Operator::BitOr => Type::new_big_integer_literal(LiteralBigInteger {
            value: &left.value | &right.value,
        }),
        nodes::Operator::BitXor => Type::new_big_integer_literal(LiteralBigInteger {
            value: &left.value ^ &right.value,
        }),
        nodes::Operator::BitAnd => Type::new_big_integer_literal(LiteralBigInteger {
            value: &left.value & &right.value,
        }),
        nodes::Operator::MatMult => return GenExprResult::raise(Exception::type_error()),
    })
}
