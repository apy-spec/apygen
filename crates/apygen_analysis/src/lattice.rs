use std::convert::Infallible;
use std::sync::Arc;

pub trait ContextualLattice<C>: Sized {
    type Error;

    fn includes(&self, context: &C, other: &Self) -> Result<bool, Self::Error>;

    fn join(&self, context: &C, other: &Self) -> Result<Self, Self::Error>;

    fn join_assign(&mut self, context: &C, other: &Self) -> Result<(), Self::Error> {
        *self = self.join(context, other)?;
        Ok(())
    }
}

impl<C, T: ContextualLattice<C> + PartialEq + Eq> ContextualLattice<C> for Arc<T> {
    type Error = T::Error;

    fn includes(&self, context: &C, other: &Self) -> Result<bool, Self::Error> {
        if self == other {
            return Ok(true);
        }
        self.as_ref().includes(context, other.as_ref())
    }

    fn join(&self, context: &C, other: &Self) -> Result<Self, Self::Error> {
        if self == other {
            return Ok(self.clone());
        }
        Ok(Arc::new(self.as_ref().join(context, other.as_ref())?))
    }
}

impl<C, T: ContextualLattice<C> + Clone> ContextualLattice<C> for Option<T> {
    type Error = T::Error;

    fn includes(&self, context: &C, other: &Self) -> Result<bool, Self::Error> {
        Ok(match (self, other) {
            (Some(self_lattice), Some(other_lattice)) => {
                self_lattice.includes(context, other_lattice)?
            }
            (Some(_), None) => true,
            (None, Some(_)) => false,
            (None, None) => true,
        })
    }

    fn join(&self, context: &C, other: &Self) -> Result<Self, Self::Error> {
        Ok(match (self, other) {
            (Some(self_lattice), Some(other_lattice)) => {
                Some(self_lattice.join(context, other_lattice)?)
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

    fn join_assign(&mut self, other: &Self)
    where
        Self: Sized,
    {
        *self = self.join(other);
    }
}

impl<T: Lattice + PartialEq + Eq> Lattice for Arc<T> {
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

impl<T: Lattice + Clone> Lattice for Option<T> {
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

impl<C, T: InfallibleLattice> ContextualLattice<C> for T {
    type Error = Infallible;

    fn includes(&self, _context: &C, other: &Self) -> Result<bool, Self::Error> {
        Ok(self.includes(other))
    }

    fn join(&self, _context: &C, other: &Self) -> Result<Self, Self::Error> {
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
