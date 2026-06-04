use crate::abstract_environment::{Exception, LiteralBoolean, LiteralFloat, Type};
use crate::genkill::expressions::PyTypeEval;
use apygen_analysis::cfg::nodes;
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

pub fn call_unary_op(literal_float: &LiteralFloat, operator: nodes::UnaryOp) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
        nodes::UnaryOp::Invert => {
            return PyTypeEval::raise(Exception::type_error());
        }
        nodes::UnaryOp::Not => call_not(literal_float),
        nodes::UnaryOp::UAdd => call_dunder_pos(literal_float),
        nodes::UnaryOp::USub => call_dunder_neg(literal_float),
    })
}

pub fn call_binary_op(
    left: &LiteralFloat,
    operator: nodes::Operator,
    right: &LiteralFloat,
) -> PyTypeEval {
    PyTypeEval::with_default_effects(match operator {
        nodes::Operator::Add => Type::new_float_literal(LiteralFloat {
            value: left.value + right.value,
        }),
        nodes::Operator::Sub => Type::new_float_literal(LiteralFloat {
            value: left.value - right.value,
        }),
        nodes::Operator::Mult => Type::new_float_literal(LiteralFloat {
            value: left.value * right.value,
        }),
        nodes::Operator::Pow => Type::new_float_literal(LiteralFloat {
            value: left.value.pow(right.value),
        }),
        nodes::Operator::Div => {
            if right.value == 0.0 {
                return PyTypeEval::raise(Exception::builtins("ZeroDivisionError"));
            }

            Type::new_float_literal(LiteralFloat {
                value: left.value / right.value,
            })
        }
        nodes::Operator::FloorDiv => {
            if right.value == 0.0 {
                return PyTypeEval::raise(Exception::builtins("ZeroDivisionError"));
            }

            Type::new_float_literal(LiteralFloat {
                value: (left.value / right.value).floor(),
            })
        }
        nodes::Operator::Mod => {
            if right.value == 0.0 {
                return PyTypeEval::raise(Exception::builtins("ZeroDivisionError"));
            }

            Type::new_float_literal(LiteralFloat {
                value: left.value % right.value,
            })
        }
        nodes::Operator::MatMult
        | nodes::Operator::LShift
        | nodes::Operator::RShift
        | nodes::Operator::BitOr
        | nodes::Operator::BitXor
        | nodes::Operator::BitAnd => return PyTypeEval::raise(Exception::type_error()),
    })
}
