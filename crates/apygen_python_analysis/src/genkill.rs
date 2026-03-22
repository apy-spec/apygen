pub mod annotations;
pub mod assignment;
pub mod expressions;
pub mod literals;
pub mod statements;
pub mod visibility;

use crate::abstract_environment::Identifier;
use crate::analysis::cfg::nodes::{Expr, ExprAttribute, ExprName};
use apy::OneOrMany;
use apy::v1::{FromInvalidIdentifierError, QualifiedName};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ToQualifiedNameError {
    #[error("expression contains an invalid identifier")]
    InvalidIdentifier(#[from] FromInvalidIdentifierError),
    #[error("expression is not a valid qualified name expression")]
    InvalidQualifiedName,
}

pub trait ToQualifiedName {
    fn to_qualified_name(&self) -> Result<QualifiedName, ToQualifiedNameError>;
}

impl ToQualifiedName for ExprName {
    fn to_qualified_name(&self) -> Result<QualifiedName, ToQualifiedNameError> {
        Ok(QualifiedName {
            identifiers: OneOrMany::one(Identifier::try_from(self.id.as_ref())?),
        })
    }
}

impl ToQualifiedName for ExprAttribute {
    fn to_qualified_name(&self) -> Result<QualifiedName, ToQualifiedNameError> {
        let mut qualified_name = self.value.to_qualified_name()?;
        qualified_name
            .identifiers
            .push(Identifier::try_from(self.attr.id.as_ref())?);
        Ok(qualified_name)
    }
}

impl ToQualifiedName for Expr {
    fn to_qualified_name(&self) -> Result<QualifiedName, ToQualifiedNameError> {
        match self {
            Expr::Name(expr_name) => expr_name.to_qualified_name(),
            Expr::Attribute(expr_attribute) => expr_attribute.to_qualified_name(),
            _ => Err(ToQualifiedNameError::InvalidQualifiedName),
        }
    }
}
