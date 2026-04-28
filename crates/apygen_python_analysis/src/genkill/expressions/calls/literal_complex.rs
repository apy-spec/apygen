use crate::abstract_environment::{Exception, LiteralBoolean, LiteralComplex, Type};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;
use num_complex::Complex64;
use num_traits::Pow;

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

pub fn call_unary_op(
    literal_complex: &LiteralComplex,
    operator: nodes::UnaryOp,
) -> GenExprResult<Type> {
    GenExprResult::new_total_pure_non_raising(match operator {
        nodes::UnaryOp::Invert => return GenExprResult::raise(Exception::type_error()),
        nodes::UnaryOp::Not => call_not(literal_complex),
        nodes::UnaryOp::UAdd => call_dunder_pos(literal_complex),
        nodes::UnaryOp::USub => call_dunder_neg(literal_complex),
    })
}

pub fn call_binary_op(
    left: &LiteralComplex,
    operator: nodes::Operator,
    right: &LiteralComplex,
) -> GenExprResult<Type> {
    GenExprResult::new_total_pure_non_raising(match operator {
        nodes::Operator::Add => Type::new_complex_literal(LiteralComplex {
            value: left.value + right.value,
        }),
        nodes::Operator::Sub => Type::new_complex_literal(LiteralComplex {
            value: left.value - right.value,
        }),
        nodes::Operator::Mult => Type::new_complex_literal(LiteralComplex {
            value: left.value * right.value,
        }),
        nodes::Operator::Pow => Type::new_complex_literal(LiteralComplex {
            value: left.value.pow(right.value),
        }),
        nodes::Operator::Div => {
            if right.value.re == 0.0 && right.value.im == 0.0 {
                return GenExprResult::raise(Exception::builtins("ZeroDivisionError"));
            }

            Type::new_complex_literal(LiteralComplex {
                value: left.value / right.value,
            })
        }
        nodes::Operator::Mod
        | nodes::Operator::FloorDiv
        | nodes::Operator::MatMult
        | nodes::Operator::LShift
        | nodes::Operator::RShift
        | nodes::Operator::BitOr
        | nodes::Operator::BitXor
        | nodes::Operator::BitAnd => return GenExprResult::raise(Exception::type_error()),
    })
}
