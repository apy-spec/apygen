use crate::abstract_environment::{Exception, LiteralBoolean, LiteralFloat, Type};
use crate::constraints::{BinaryOperator, UnaryOperator};
use crate::genkill::expressions::PyTypeEval;
use num_traits::Pow;

pub fn as_boolean(literal_float: &LiteralFloat) -> bool {
    literal_float.value != 0.0
}

pub fn call_dunder_bool(literal_float: &LiteralFloat) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_float),
    })
}

pub fn call_not(literal_float: &LiteralFloat) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
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

pub fn call_unary_op(literal_float: &LiteralFloat, operator: UnaryOperator) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
        UnaryOperator::Invert => {
            return PyTypeEval::raise(Exception::any()); // TODO: fix
        }
        UnaryOperator::Not => call_not(literal_float),
        UnaryOperator::UAdd => call_dunder_pos(literal_float),
        UnaryOperator::USub => call_dunder_neg(literal_float),
    })
}

pub fn call_binary_op(
    left: &LiteralFloat,
    operator: BinaryOperator,
    right: &LiteralFloat,
) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
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
    })
}
