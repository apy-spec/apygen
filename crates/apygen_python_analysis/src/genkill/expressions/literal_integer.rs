use crate::abstract_environment::{Exception, LiteralBoolean, LiteralFloat, LiteralInteger, Type};
use crate::genkill::expressions;
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;
use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{Pow, ToPrimitive};

pub fn as_boolean(literal_integer: &LiteralInteger) -> bool {
    match literal_integer {
        LiteralInteger::Int(value) => *value != 0,
        LiteralInteger::BigInt(value) => value != &BigInt::ZERO,
    }
}

pub fn call_dunder_float(literal_integer: &LiteralInteger) -> GenExprResult<Type> {
    if let Some(literal_float) = literal_integer.to_literal_float() {
        GenExprResult::new_total_pure_non_raising(Type::new_float_literal(literal_float))
    } else {
        GenExprResult::unknown()
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
            let big_right = match right {
                LiteralInteger::Int(small_right) => {
                    if let Ok(small_right) = usize::try_from(*small_right) {
                        return GenExprResult::new_total_pure_non_raising(
                            Type::new_integer_literal(left.pow(small_right)),
                        );
                    }
                    &BigInt::from(*small_right)
                }
                LiteralInteger::BigInt(big_right) => big_right,
            };

            if let Some(big_right) = big_right.to_biguint() {
                Type::new_integer_literal(left.pow(big_right))
            } else if let (Some(left_float), Some(right_float)) = (left.to_f64(), right.to_f64()) {
                // Handle negative powers
                return expressions::literal_float::call_binary_op(
                    &LiteralFloat { value: left_float },
                    nodes::Operator::Pow,
                    &LiteralFloat { value: right_float },
                );
            } else {
                return GenExprResult::unknown();
            }
        }
        nodes::Operator::Div => {
            if right.is_zero() {
                return GenExprResult::raise(Exception::builtins("ZeroDivisionError"));
            }

            let (left, right) = match (left, right) {
                (LiteralInteger::Int(left), LiteralInteger::Int(right)) => {
                    if let Some(value) = Rational64::new(*left, *right).to_f64() {
                        return GenExprResult::new_total_pure_non_raising(Type::new_float_literal(
                            LiteralFloat { value },
                        ));
                    }
                    (&BigInt::from(*left), &BigInt::from(*right))
                }
                (LiteralInteger::Int(left), LiteralInteger::BigInt(right)) => {
                    (&BigInt::from(*left), right)
                }
                (LiteralInteger::BigInt(left), LiteralInteger::Int(right)) => {
                    (left, &BigInt::from(*right))
                }
                (LiteralInteger::BigInt(left), LiteralInteger::BigInt(right)) => (left, right),
            };

            let Some(value) = BigRational::new(left.clone(), right.clone()).to_f64() else {
                return GenExprResult::unknown();
            };

            Type::new_float_literal(LiteralFloat { value })
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
