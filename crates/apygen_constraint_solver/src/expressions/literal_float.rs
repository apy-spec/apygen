use crate::EvaluationState;
use crate::analysis::abstract_state::AbstractState;
use crate::constraint_graph::expressions::{BinaryOperator, UnaryOperator};
use crate::expressions::PyTypeEval;
use crate::identifiers::Namespace;
use crate::inference::{Exception, Sourced, Type};
use crate::primitives::Pow;
use crate::primitives::literals::{LiteralBool, LiteralFloat};

pub fn as_boolean(literal_float: &LiteralFloat) -> bool {
    literal_float.value != 0.0
}

pub fn call_dunder_bool(literal_float: &LiteralFloat) -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: as_boolean(literal_float),
    })
}

pub fn call_not(literal_float: &LiteralFloat) -> Type {
    Type::new_boolean_literal(LiteralBool {
        value: !as_boolean(literal_float),
    })
}

pub fn call_dunder_pos(literal_float: &LiteralFloat) -> Type {
    Type::new_float_literal(LiteralFloat {
        value: literal_float.value,
    })
}

pub fn call_dunder_neg(literal_float: &LiteralFloat) -> Type {
    Type::new_float_literal(LiteralFloat {
        value: -literal_float.value,
    })
}

pub fn call_unary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    literal_float: &LiteralFloat,
    operator: UnaryOperator,
) -> PyTypeEval<S> {
    PyTypeEval::with_default_effects(Sourced::inferred(match operator {
        UnaryOperator::Invert => {
            return PyTypeEval::raise(Exception::any()); // TODO: fix
        }
        UnaryOperator::Not => call_not(literal_float),
        UnaryOperator::UAdd => call_dunder_pos(literal_float),
        UnaryOperator::USub => call_dunder_neg(literal_float),
    }))
}

pub fn call_binary_op<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>>(
    left: &LiteralFloat,
    operator: BinaryOperator,
    right: &LiteralFloat,
) -> PyTypeEval<S> {
    PyTypeEval::with_default_effects(Sourced::inferred(match operator {
        BinaryOperator::Add => Type::new_float_literal(LiteralFloat {
            value: left.value + right.value,
        }),
        BinaryOperator::Sub => Type::new_float_literal(LiteralFloat {
            value: left.value - right.value,
        }),
        BinaryOperator::Mult => Type::new_float_literal(LiteralFloat {
            value: left.value * right.value,
        }),
        BinaryOperator::Pow => Type::new_float_literal(LiteralFloat {
            value: left.value.pow(right.value),
        }),
        BinaryOperator::Div => {
            if right.value == 0.0 {
                return PyTypeEval::raise(Exception::any()); // TODO: fix
            }

            Type::new_float_literal(LiteralFloat {
                value: left.value / right.value,
            })
        }
        BinaryOperator::FloorDiv => {
            if right.value == 0.0 {
                return PyTypeEval::raise(Exception::any()); // TODO: fix
            }

            Type::new_float_literal(LiteralFloat {
                value: (left.value / right.value).floor(),
            })
        }
        BinaryOperator::Mod => {
            if right.value == 0.0 {
                return PyTypeEval::raise(Exception::any()); // TODO: fix
            }

            Type::new_float_literal(LiteralFloat {
                value: left.value % right.value,
            })
        }
        BinaryOperator::MatMult
        | BinaryOperator::LShift
        | BinaryOperator::RShift
        | BinaryOperator::BitOr
        | BinaryOperator::BitXor
        | BinaryOperator::BitAnd => return PyTypeEval::raise(Exception::any()), // TODO: fix,
        _ => todo!(),
    }))
}
