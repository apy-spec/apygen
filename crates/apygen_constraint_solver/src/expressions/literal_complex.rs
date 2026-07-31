use crate::EvaluationState;
use crate::analysis::abstract_state::AbstractState;
use crate::constraint_graph::expressions::{BinaryOperator, UnaryOperator};
use crate::expressions::PyTypeEval;
use crate::identifiers::Namespace;
use crate::inference::{Exception, Sourced, Type};
use crate::primitives::Complex64;
use crate::primitives::Pow;
use crate::primitives::literals::{LiteralBool, LiteralComplex};

pub fn as_boolean(literal_complex: &LiteralComplex) -> bool {
    literal_complex.value.re != 0.0 || literal_complex.value.im != 0.0
}

pub fn call_dunder_bool(literal_complex: &LiteralComplex) -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: as_boolean(literal_complex),
    })
}

pub fn call_not(literal_complex: &LiteralComplex) -> Type {
    Type::new_boolean_literal(LiteralBool {
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

pub fn call_unary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    literal_complex: &LiteralComplex,
    operator: UnaryOperator,
) -> PyTypeEval<S> {
    PyTypeEval::with_default_effects(Sourced::inferred(match operator {
        UnaryOperator::Invert => {
            return PyTypeEval::raise(Exception::any()); // TODO: fix
        }
        UnaryOperator::Not => call_not(literal_complex),
        UnaryOperator::UAdd => call_dunder_pos(literal_complex),
        UnaryOperator::USub => call_dunder_neg(literal_complex),
    }))
}

pub fn call_binary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    left: &LiteralComplex,
    operator: BinaryOperator,
    right: &LiteralComplex,
) -> PyTypeEval<S> {
    PyTypeEval::with_default_effects(Sourced::inferred(match operator {
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
                return PyTypeEval::raise(Exception::any()); // TODO: fix
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
            return PyTypeEval::raise(Exception::any()); // TODO: fix
        }
        _ => todo!(),
    }))
}
