use crate::abstract_environment::{
    Exception, ExceptionOrigin, LiteralBoolean, LiteralFloat, LiteralInteger, Type,
};
use crate::constraints::{BinaryOperator, UnaryOperator};
use crate::genkill::expressions;
use crate::genkill::expressions::PyTypeEval;
use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{Pow, ToPrimitive};

pub fn as_boolean(literal_integer: &LiteralInteger) -> bool {
    match literal_integer {
        LiteralInteger::Int(value) => *value != 0,
        LiteralInteger::BigInt(value) => value != &BigInt::ZERO,
    }
}

pub fn call_dunder_float(literal_integer: &LiteralInteger) -> PyTypeEval {
    if let Some(literal_float) = literal_integer.to_literal_float() {
        PyTypeEval::with_default_effects(Type::new_float_literal(literal_float))
    } else {
        PyTypeEval::unknown()
    }
}

pub fn call_dunder_int(literal_integer: &LiteralInteger) -> Type {
    Type::new_integer_literal(literal_integer.clone())
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

pub fn call_unary_op(literal_integer: &LiteralInteger, operator: UnaryOperator) -> Type {
    match operator {
        UnaryOperator::Invert => call_dunder_invert(literal_integer),
        UnaryOperator::Not => call_not(literal_integer),
        UnaryOperator::UAdd => call_dunder_pos(literal_integer),
        UnaryOperator::USub => call_dunder_neg(literal_integer),
    }
}

pub fn call_binary_op(
    left: &LiteralInteger,
    operator: BinaryOperator,
    right: &LiteralInteger,
) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
        BinaryOperator::Add => Type::new_integer_literal(left + right),
        BinaryOperator::Sub => Type::new_integer_literal(left - right),
        BinaryOperator::Mult => Type::new_integer_literal(left * right),
        BinaryOperator::Pow => {
            let big_right = match right {
                LiteralInteger::Int(small_right) => {
                    if let Ok(small_right) = usize::try_from(*small_right) {
                        return PyTypeEval::with_default_effects(Type::new_integer_literal(
                            left.pow(small_right),
                        ));
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
                    BinaryOperator::Pow,
                    &LiteralFloat { value: right_float },
                );
            } else {
                return PyTypeEval::unknown();
            }
        }
        BinaryOperator::Div => {
            if right.is_zero() {
                return PyTypeEval::raise(Exception::builtins(
                    "ZeroDivisionError",
                    ExceptionOrigin::Unknown,
                ));
            }

            let (left, right) = match (left, right) {
                (LiteralInteger::Int(left), LiteralInteger::Int(right)) => {
                    if let Some(value) = Rational64::new(*left, *right).to_f64() {
                        return PyTypeEval::with_default_effects(Type::new_float_literal(
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
                return PyTypeEval::unknown();
            };

            Type::new_float_literal(LiteralFloat { value })
        }
        BinaryOperator::FloorDiv => {
            if right.is_zero() {
                return PyTypeEval::raise(Exception::builtins(
                    "ZeroDivisionError",
                    ExceptionOrigin::Unknown,
                ));
            }

            Type::new_integer_literal(left / right)
        }
        BinaryOperator::Mod => {
            if right.is_zero() {
                return PyTypeEval::raise(Exception::builtins(
                    "ZeroDivisionError",
                    ExceptionOrigin::Unknown,
                ));
            }

            Type::new_integer_literal(left % right)
        }
        BinaryOperator::LShift => match right {
            LiteralInteger::Int(small_right) => {
                if let Ok(small_right) = usize::try_from(*small_right) {
                    Type::new_integer_literal(left << small_right)
                } else if let Ok(small_right) = isize::try_from(*small_right) {
                    Type::new_integer_literal(left << small_right)
                } else {
                    return PyTypeEval::unknown();
                }
            }
            LiteralInteger::BigInt(_) => {
                return PyTypeEval::unknown();
            }
        },
        BinaryOperator::RShift => match right {
            LiteralInteger::Int(small_right) => {
                if let Ok(small_right) = usize::try_from(*small_right) {
                    Type::new_integer_literal(left >> small_right)
                } else if let Ok(small_right) = isize::try_from(*small_right) {
                    Type::new_integer_literal(left >> small_right)
                } else {
                    return PyTypeEval::unknown();
                }
            }
            LiteralInteger::BigInt(_) => {
                return PyTypeEval::unknown();
            }
        },
        BinaryOperator::BitOr => Type::new_integer_literal(left | right),
        BinaryOperator::BitXor => Type::new_integer_literal(left ^ right),
        BinaryOperator::BitAnd => Type::new_integer_literal(left & right),
        BinaryOperator::MatMult => {
            return PyTypeEval::raise(Exception::type_error(ExceptionOrigin::Unknown));
        }
        _ => return PyTypeEval::unknown(),
    })
}
