use crate::abstract_environment::{
    Exception, LiteralBoolean, LiteralBytes, OneOrMany, QualifiedName, Type,
    new_identifier_or_panic,
};
use crate::genkill::expressions::GenExprResult;
use apygen_analysis::cfg::nodes;

pub fn as_boolean(literal_bytes: &LiteralBytes) -> bool {
    !literal_bytes.value.is_empty()
}

pub fn call_dunder_bool(literal_bytes: &LiteralBytes) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: as_boolean(literal_bytes),
    })
}

pub fn call_not(literal_bytes: &LiteralBytes) -> Type {
    Type::new_boolean_literal(LiteralBoolean {
        value: !as_boolean(literal_bytes),
    })
}

pub fn call_unary_op(
    literal_bytes: &LiteralBytes,
    operator: nodes::UnaryOp,
) -> GenExprResult<Type> {
    match operator {
        nodes::UnaryOp::Invert | nodes::UnaryOp::UAdd | nodes::UnaryOp::USub => {
            GenExprResult::raise(Exception::from_type(Type::Reference {
                name: QualifiedName {
                    identifiers: OneOrMany::one(new_identifier_or_panic("TypeError")),
                },
                arguments: imbl::Vector::new(),
                origin: None,
            }))
        }
        nodes::UnaryOp::Not => GenExprResult::new_total_pure_non_raising(call_not(literal_bytes)),
    }
}
