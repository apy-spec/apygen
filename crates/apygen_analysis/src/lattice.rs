use crate::namespace::Namespaces;
use std::hash::Hash;
use std::sync::Arc;

pub trait NamespacesLattice<M: Clone + PartialEq + Eq + Hash, E: Clone + Default>: Sized {
    type Error;

    fn includes(
        &self,
        namespaces: &impl Namespaces<M, E>,
        other: &Self,
    ) -> Result<bool, Self::Error>;

    fn join(&self, namespaces: &impl Namespaces<M, E>, other: &Self) -> Result<Self, Self::Error>;
}

impl<
    M: Clone + PartialEq + Eq + Hash,
    E: Clone + Default,
    L: NamespacesLattice<M, E> + PartialEq + Eq,
> NamespacesLattice<M, E> for Arc<L>
{
    type Error = L::Error;

    fn includes(
        &self,
        namespaces: &impl Namespaces<M, E>,
        other: &Self,
    ) -> Result<bool, Self::Error> {
        if self == other {
            return Ok(true);
        }
        self.as_ref().includes(namespaces, other)
    }

    fn join(&self, namespaces: &impl Namespaces<M, E>, other: &Self) -> Result<Self, Self::Error> {
        if self == other {
            return Ok(self.clone());
        }
        Ok(Arc::new(self.as_ref().join(namespaces, other)?))
    }
}

pub trait Lattice {
    fn includes(&self, other: &Self) -> bool;

    fn join(&self, other: &Self) -> Self;
}

impl<L: Lattice + PartialEq + Eq> Lattice for Arc<L> {
    fn includes(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        self.as_ref().includes(other.as_ref())
    }

    fn join(&self, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }
        Arc::new(self.as_ref().join(other.as_ref()))
    }
}

pub trait OrdLattice: PartialEq + Eq + PartialOrd + Ord + Clone {}

impl<T: OrdLattice> Lattice for T {
    fn includes(&self, other: &Self) -> bool {
        other <= self
    }

    fn join(&self, other: &Self) -> Self {
        self.max(other).clone()
    }
}
