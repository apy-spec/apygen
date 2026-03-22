use crate::namespace::NamespacesContext;
use std::hash::Hash;

pub trait Lattice<M: Clone + PartialEq + Eq + Hash>
where
    Self: Clone + Default,
{
    type ContextError;

    fn includes(
        &self,
        context: &impl NamespacesContext<M, Self>,
        other: &Self,
    ) -> Result<bool, Self::ContextError>;

    fn join(
        &self,
        context: &impl NamespacesContext<M, Self>,
        other: &Self,
    ) -> Result<Self, Self::ContextError>;
}
