use crate::abstract_environment::{Exception, LiteralBoolean, LiteralInteger, Type};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;
use num_bigint::BigInt;
use num_traits::Pow;

pub fn as_boolean(literal_integer: &LiteralInteger) -> bool {
    match literal_integer {
        LiteralInteger::Int(value) => *value != 0,
        LiteralInteger::BigInt(value) => value != &BigInt::ZERO,
    }
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
    Type::new_integer_literal(literal_integer.clone())
}

pub fn call_dunder_neg(literal_integer: &LiteralInteger) -> Type {
    Type::new_integer_literal(-literal_integer)
}

pub fn call_dunder_invert(literal_integer: &LiteralInteger) -> Type {
    Type::new_integer_literal(!literal_integer)
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
        nodes::Operator::Add => Type::new_integer_literal(left + right),
        nodes::Operator::Sub => Type::new_integer_literal(left - right),
        nodes::Operator::Mult => Type::new_integer_literal(left * right),
        nodes::Operator::Pow => {
            match right {
                LiteralInteger::Int(small_right) => {
                    if let Ok(small_right) = usize::try_from(*small_right) {
                        Type::new_integer_literal(left.pow(small_right))
                    } else {
                        // TODO: this should call the float implementation of Pow
                        return GenExprResult::unknown();
                    }
                }
                LiteralInteger::BigInt(big_right) => {
                    if let Some(big_right) = big_right.to_biguint() {
                        Type::new_integer_literal(left.pow(big_right))
                    } else {
                        // TODO: this should call the float implementation of Pow
                        return GenExprResult::unknown();
                    }
                }
            }
        }
        nodes::Operator::Div => {
            // TODO: this should call the float implementation of Div
            return GenExprResult::unknown();
        }
        nodes::Operator::FloorDiv => {
            if right.is_zero() {
                return GenExprResult::raise(Exception::builtins("ZeroDivisionError"));
            }

            Type::new_integer_literal(left / right)
        }
        nodes::Operator::Mod => {
            if right.is_zero() {
                return GenExprResult::raise(Exception::builtins("ZeroDivisionError"));
            }

            Type::new_integer_literal(left % right)
        }
        nodes::Operator::LShift => match right {
            LiteralInteger::Int(small_right) => {
                if let Ok(small_right) = usize::try_from(*small_right) {
                    Type::new_integer_literal(left << small_right)
                } else if let Ok(small_right) = isize::try_from(*small_right) {
                    Type::new_integer_literal(left << small_right)
                } else {
                    return GenExprResult::unknown();
                }
            }
            LiteralInteger::BigInt(_) => {
                return GenExprResult::unknown();
            }
        },
        nodes::Operator::RShift => match right {
            LiteralInteger::Int(small_right) => {
                if let Ok(small_right) = usize::try_from(*small_right) {
                    Type::new_integer_literal(left >> small_right)
                } else if let Ok(small_right) = isize::try_from(*small_right) {
                    Type::new_integer_literal(left >> small_right)
                } else {
                    return GenExprResult::unknown();
                }
            }
            LiteralInteger::BigInt(_) => {
                return GenExprResult::unknown();
            }
        },
        nodes::Operator::BitOr => Type::new_integer_literal(left | right),
        nodes::Operator::BitXor => Type::new_integer_literal(left ^ right),
        nodes::Operator::BitAnd => Type::new_integer_literal(left & right),
        nodes::Operator::MatMult => return GenExprResult::raise(Exception::type_error()),
    })
}
