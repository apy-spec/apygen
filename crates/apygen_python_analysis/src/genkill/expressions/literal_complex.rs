use crate::abstract_environment::{
    Exception, ExceptionOrigin, LiteralBoolean, LiteralComplex, Type,
};
use crate::genkill::expressions::PyTypeEval;
use num_complex::Complex64;
use num_traits::Pow;
use crate::constraints::{BinaryOperator, UnaryOperator};

pub fn as_boolean(literal_complex: &LiteralComplex) -> bool {
    literal_complex.value.re != 0.0 || literal_complex.value.im != 0.0
}

pub fn call_dunder_bool(literal_complex: &LiteralComplex) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_complex),
    })
}

pub fn call_not(literal_complex: &LiteralComplex) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_complex),
    })
}

pub fn call_dunder_pos(literal_complex: &LiteralComplex) -> Type {
    Type::new_complex_literal(literal_complex.clone())
}

pub fn call_dunder_neg(literal_complex: &LiteralComplex) -> Type {
    Type::new_complex_literal(LiteralComplex {
        value: Complex64::new(-literal_complex.value.re, -literal_complex.value.im),
    })
}

pub fn call_unary_op(literal_complex: &LiteralComplex, operator: UnaryOperator) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
        UnaryOperator::Invert => {
            return PyTypeEval::raise(Exception::type_error(ExceptionOrigin::Unknown));
        }
        UnaryOperator::Not => call_not(literal_complex),
        UnaryOperator::UAdd => call_dunder_pos(literal_complex),
        UnaryOperator::USub => call_dunder_neg(literal_complex),
    })
}

pub fn call_binary_op(
    left: &LiteralComplex,
    operator: BinaryOperator,
    right: &LiteralComplex,
) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
        BinaryOperator::Add => Type::new_complex_literal(LiteralComplex {
            value: left.value + right.value,
        }),
        BinaryOperator::Sub => Type::new_complex_literal(LiteralComplex {
            value: left.value - right.value,
        }),
        BinaryOperator::Mult => Type::new_complex_literal(LiteralComplex {
            value: left.value * right.value,
        }),
        BinaryOperator::Pow => Type::new_complex_literal(LiteralComplex {
            value: left.value.pow(right.value),
        }),
        BinaryOperator::Div => {
            if right.value.re == 0.0 && right.value.im == 0.0 {
                return PyTypeEval::raise(Exception::builtins(
                    "ZeroDivisionError",
                    ExceptionOrigin::Unknown,
                ));
            }

            Type::new_complex_literal(LiteralComplex {
                value: left.value / right.value,
            })
        }
        BinaryOperator::Mod
        | BinaryOperator::FloorDiv
        | BinaryOperator::MatMult
        | BinaryOperator::LShift
        | BinaryOperator::RShift
        | BinaryOperator::BitOr
        | BinaryOperator::BitXor
        | BinaryOperator::BitAnd => {
            return PyTypeEval::raise(Exception::type_error(ExceptionOrigin::Unknown));
        },
        _ => todo!()
    })
}
