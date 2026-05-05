use crate::namespace::Namespaces;
use std::convert::Infallible;
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

impl<
    M: Clone + PartialEq + Eq + Hash,
    E: Clone + Default,
    L: NamespacesLattice<M, E> + PartialEq + Eq + Clone,
> NamespacesLattice<M, E> for Option<L>
{
    type Error = L::Error;

    fn includes(
        &self,
        namespaces: &impl Namespaces<M, E>,
        other: &Self,
    ) -> Result<bool, Self::Error> {
        Ok(match (self, other) {
            (Some(self_lattice), Some(other_lattice)) => {
                self_lattice.includes(namespaces, other_lattice)?
            }
            (Some(_), None) => true,
            (None, Some(_)) => false,
            (None, None) => true,
        })
    }

    fn join(&self, namespaces: &impl Namespaces<M, E>, other: &Self) -> Result<Self, Self::Error> {
        Ok(match (self, other) {
            (Some(self_lattice), Some(other_lattice)) => {
                Some(self_lattice.join(namespaces, other_lattice)?)
            }
            (Some(self_lattice), None) => Some(self_lattice.clone()),
            (None, Some(other_lattice)) => Some(other_lattice.clone()),
            (None, None) => None,
        })
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

impl<L: Lattice + PartialEq + Eq + Clone> Lattice for Option<L> {
    fn includes(&self, other: &Self) -> bool {
        match (self, other) {
            (Some(self_lattice), Some(other_lattice)) => self_lattice.includes(other_lattice),
            (Some(_), None) => true,
            (None, Some(_)) => false,
            (None, None) => true,
        }
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Some(self_lattice), Some(other_lattice)) => Some(self_lattice.join(other_lattice)),
            (Some(self_lattice), None) => Some(self_lattice.clone()),
            (None, Some(other_lattice)) => Some(other_lattice.clone()),
            (None, None) => None,
        }
    }
}

pub trait InfallibleLattice: Lattice {}

impl<L: InfallibleLattice, M: Clone + PartialEq + Eq + Hash, E: Clone + Default>
    NamespacesLattice<M, E> for L
{
    type Error = Infallible;

    fn includes(
        &self,
        _namespaces: &impl Namespaces<M, E>,
        other: &Self,
    ) -> Result<bool, Self::Error> {
        Ok(self.includes(other))
    }

    fn join(&self, _namespaces: &impl Namespaces<M, E>, other: &Self) -> Result<Self, Self::Error> {
        Ok(self.join(other))
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
