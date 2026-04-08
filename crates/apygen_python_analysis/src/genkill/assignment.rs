use crate::analysis::cfg::nodes::{
    Expr, ExprAttribute, ExprList, ExprName, ExprStarred, ExprSubscript, ExprTuple,
};
use crate::abstract_environment::{ParseIdentifierError, Identifier};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum FromAssignmentTargetError {
    #[error("the expression contains an invalid identifier")]
    InvalidIdentifier(#[from] ParseIdentifierError),
    #[error("the expression is not a valid assignment target")]
    InvalidTarget,
}

pub enum AssignmentTarget<'e> {
    Name(Identifier),
    Attribute {
        target: Box<AssignmentTarget<'e>>,
        attr: Identifier,
    },
    Subscript {
        target: Box<AssignmentTarget<'e>>,
        slice: &'e Expr,
    },
    Starred(Box<AssignmentTarget<'e>>),
    Tuple(Vec<AssignmentTarget<'e>>),
    List(Vec<AssignmentTarget<'e>>),
}

impl TryFrom<&ExprName> for AssignmentTarget<'_> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &ExprName) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Name(Identifier::try_from(
            value.id.as_ref(),
        )?))
    }
}

impl<'e> TryFrom<&'e ExprAttribute> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ExprAttribute) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Attribute {
            attr: Identifier::try_from(value.attr.id.as_ref())?,
            target: Box::new(AssignmentTarget::try_from(value.value.as_ref())?),
        })
    }
}

impl<'e> TryFrom<&'e ExprSubscript> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ExprSubscript) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Subscript {
            slice: &value.slice,
            target: Box::new(AssignmentTarget::try_from(value.value.as_ref())?),
        })
    }
}

impl<'e> TryFrom<&'e ExprStarred> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ExprStarred) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Starred(Box::new(
            AssignmentTarget::try_from(value.value.as_ref())?,
        )))
    }
}

impl<'e> TryFrom<&'e ExprTuple> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ExprTuple) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::Tuple(
            value
                .elts
                .iter()
                .map(|element| AssignmentTarget::try_from(element))
                .collect::<Result<Vec<AssignmentTarget>, Self::Error>>()?,
        ))
    }
}

impl<'e> TryFrom<&'e ExprList> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e ExprList) -> Result<Self, Self::Error> {
        Ok(AssignmentTarget::List(
            value
                .elts
                .iter()
                .map(|element| AssignmentTarget::try_from(element))
                .collect::<Result<Vec<AssignmentTarget>, Self::Error>>()?,
        ))
    }
}

impl<'e> TryFrom<&'e Expr> for AssignmentTarget<'e> {
    type Error = FromAssignmentTargetError;

    fn try_from(value: &'e Expr) -> Result<Self, Self::Error> {
        match value {
            Expr::Name(expr_name) => AssignmentTarget::try_from(expr_name),
            Expr::Attribute(expr_attribute) => AssignmentTarget::try_from(expr_attribute),
            Expr::Subscript(expr_subscript) => AssignmentTarget::try_from(expr_subscript),
            Expr::Starred(expr_starred) => AssignmentTarget::try_from(expr_starred),
            Expr::Tuple(expr_tuple) => AssignmentTarget::try_from(expr_tuple),
            Expr::List(expr_list) => AssignmentTarget::try_from(expr_list),
            _ => Err(FromAssignmentTargetError::InvalidTarget),
        }
    }
}
