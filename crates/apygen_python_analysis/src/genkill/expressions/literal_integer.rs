use crate::abstract_environment::{Exception, LiteralBoolean, LiteralFloat, LiteralInteger, Type};
use crate::constraints::{BinaryOperator, UnaryOperator};
use crate::genkill::expressions::PyTypeEval;
use crate::primitives::Zero;
use apygen_primitives::{Pow, PowOutput};

pub fn as_boolean(literal_integer: &LiteralInteger) -> bool {
    !literal_integer.value.is_zero()
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
    Type::new_integer_literal(LiteralInteger::new(-&literal_integer.value))
}

pub fn call_dunder_invert(literal_integer: &LiteralInteger) -> Type {
    Type::new_integer_literal(LiteralInteger::new(!&literal_integer.value))
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
    let left_int = &left.value;
    let right_int = &right.value;
    PyTypeEval::with_default_effects(match operator {
        BinaryOperator::Add => Type::new_integer_literal(LiteralInteger::new(left_int + right_int)),
        BinaryOperator::Sub => Type::new_integer_literal(LiteralInteger::new(left_int - right_int)),
        BinaryOperator::Mult => {
            Type::new_integer_literal(LiteralInteger::new(left_int * right_int))
        }
        BinaryOperator::Pow => match left_int.pow(right_int) {
            Some(PowOutput::Int(value)) => Type::new_integer_literal(LiteralInteger::new(value)),
            Some(PowOutput::Float(value)) => Type::new_float_literal(LiteralFloat::new(value)),
            None => return PyTypeEval::unknown(),
        },
        BinaryOperator::Div => {
            if right_int.is_zero() {
                return PyTypeEval::raise(Exception::any()); // TODO: fix
            }

            let Some(value) = left_int.true_div(&right_int) else {
                return PyTypeEval::unknown();
            };

            Type::new_float_literal(LiteralFloat { value })
        }
        BinaryOperator::FloorDiv => {
            if right_int.is_zero() {
                return PyTypeEval::raise(Exception::any()); // TODO: fix
            }

            Type::new_integer_literal(LiteralInteger::new(left_int / right_int))
        }
        BinaryOperator::Mod => {
            if right_int.is_zero() {
                return PyTypeEval::raise(Exception::any()); // TODO: fix
            }

            Type::new_integer_literal(LiteralInteger::new(left_int % right_int))
        }
        BinaryOperator::LShift => {
            if let Some(value) = left_int << right_int {
                Type::new_integer_literal(LiteralInteger::new(value))
            } else {
                return PyTypeEval::unknown();
            }
        }
        BinaryOperator::RShift => {
            if let Some(value) = left_int >> right_int {
                Type::new_integer_literal(LiteralInteger::new(value))
            } else {
                return PyTypeEval::unknown();
            }
        }
        BinaryOperator::BitOr => {
            Type::new_integer_literal(LiteralInteger::new(left_int | right_int))
        }
        BinaryOperator::BitXor => {
            Type::new_integer_literal(LiteralInteger::new(left_int ^ right_int))
        }
        BinaryOperator::BitAnd => {
            Type::new_integer_literal(LiteralInteger::new(left_int & right_int))
        }
        BinaryOperator::MatMult => {
            return PyTypeEval::raise(Exception::any()); // TODO: fix
        }
        _ => return PyTypeEval::unknown(),
    })
}
