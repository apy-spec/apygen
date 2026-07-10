use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, btree_map, hash_map};
use std::convert::Infallible;
use std::hash::Hash;
use std::sync::Arc;

pub trait ContextualLattice<C>: Sized {
    type Error;

    fn includes(&self, context: &C, other: &Self) -> Result<bool, Self::Error>;

    fn join(&self, context: &C, other: &Self) -> Result<Self, Self::Error>;
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

pub trait LatticeOrd {
    fn leq(&self, other: &Self) -> bool;
}

impl<T: LatticeOrd> LatticeOrd for Arc<T> {
    fn leq(&self, other: &Self) -> bool {
        self.as_ref().leq(other.as_ref())
    }
}

impl<T: LatticeOrd> LatticeOrd for Option<T> {
    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Some(self_lattice), Some(other_lattice)) => self_lattice.leq(other_lattice),
            (Some(_), None) => false,
            (None, Some(_)) => true,
            (None, None) => true,
        }
    }
}

impl<T: Ord> LatticeOrd for BTreeSet<T> {
    fn leq(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<K: Ord, V: LatticeOrd> LatticeOrd for BTreeMap<K, V> {
    fn leq(&self, other: &Self) -> bool {
        self.iter().all(|(key, self_value)| {
            other
                .get(key)
                .is_some_and(|other_value| self_value.leq(other_value))
        })
    }
}

impl<T: Eq + Hash> LatticeOrd for HashSet<T> {
    fn leq(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<K: Eq + Hash, V: LatticeOrd> LatticeOrd for HashMap<K, V> {
    fn leq(&self, other: &Self) -> bool {
        self.iter().all(|(key, self_value)| {
            other
                .get(key)
                .is_some_and(|other_value| self_value.leq(other_value))
        })
    }
}

pub trait OrdLatticeOrd: Ord {}

impl<T: OrdLatticeOrd> LatticeOrd for T {
    fn leq(&self, other: &Self) -> bool {
        self <= other
    }
}

pub trait Join {
    fn join(&self, other: &Self) -> Self;
}

impl<T: Join + Eq> Join for Arc<T> {
    fn join(&self, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }
        Arc::new(self.as_ref().join(other.as_ref()))
    }
}

impl<T: Join + Clone> Join for Option<T> {
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Some(self_lattice), Some(other_lattice)) => Some(self_lattice.join(other_lattice)),
            (Some(self_lattice), None) => Some(self_lattice.clone()),
            (None, Some(other_lattice)) => Some(other_lattice.clone()),
            (None, None) => None,
        }
    }
}

impl<T: Clone + Ord> Join for BTreeSet<T> {
    fn join(&self, other: &Self) -> Self {
        if self == other {
            self.clone()
        } else {
            BTreeSet::from_iter(self.union(other).cloned())
        }
    }
}

impl<K: Clone + Ord, V: Join + Clone + Eq> Join for BTreeMap<K, V> {
    fn join(&self, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }

        let mut out = self.clone();
        for (key, value) in other {
            match out.entry(key.clone()) {
                btree_map::Entry::Vacant(entry) => {
                    entry.insert(value.clone());
                }
                btree_map::Entry::Occupied(entry) => {
                    let current = entry.into_mut();
                    *current = current.join(value);
                }
            }
        }
        out
    }
}

impl<T: Clone + Eq + Hash> Join for HashSet<T> {
    fn join(&self, other: &Self) -> Self {
        if self == other {
            self.clone()
        } else {
            HashSet::from_iter(self.union(other).cloned())
        }
    }
}

impl<K: Clone + Eq + Hash, V: Join + Clone + Eq> Join for HashMap<K, V> {
    fn join(&self, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }

        let mut out = self.clone();
        for (key, value) in other {
            match out.entry(key.clone()) {
                hash_map::Entry::Vacant(entry) => {
                    entry.insert(value.clone());
                }
                hash_map::Entry::Occupied(entry) => {
                    let current = entry.into_mut();
                    *current = current.join(value);
                }
            }
        }
        out
    }
}

pub trait OrdJoin: Ord + Clone {}

impl<T: OrdJoin> Join for T {
    fn join(&self, other: &Self) -> Self {
        self.max(other).clone()
    }
}

pub trait Meet {
    fn meet(&self, other: &Self) -> Self;
}

impl<T: Meet + Eq> Meet for Arc<T> {
    fn meet(&self, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }
        Arc::new(self.as_ref().meet(other.as_ref()))
    }
}

impl<T: Meet + Clone> Meet for Option<T> {
    fn meet(&self, other: &Self) -> Self {
        match (self, other) {
            (Some(self_lattice), Some(other_lattice)) => Some(self_lattice.meet(other_lattice)),
            _ => None,
        }
    }
}

impl<T: Clone + Ord> Meet for BTreeSet<T> {
    fn meet(&self, other: &Self) -> Self {
        if self == other {
            self.clone()
        } else {
            BTreeSet::from_iter(self.union(other).cloned())
        }
    }
}

impl<K: Clone + Ord, V: Meet + Clone + Eq> Meet for BTreeMap<K, V> {
    fn meet(&self, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }

        let mut out = self.clone();
        for (key, value) in other {
            match out.entry(key.clone()) {
                btree_map::Entry::Vacant(entry) => {
                    entry.insert(value.clone());
                }
                btree_map::Entry::Occupied(entry) => {
                    let current = entry.into_mut();
                    *current = current.meet(value);
                }
            }
        }
        out
    }
}

impl<T: Clone + Eq + Hash> Meet for HashSet<T> {
    fn meet(&self, other: &Self) -> Self {
        if self == other {
            self.clone()
        } else {
            HashSet::from_iter(self.union(other).cloned())
        }
    }
}

impl<K: Clone + Eq + Hash, V: Meet + Clone + Eq> Meet for HashMap<K, V> {
    fn meet(&self, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }

        let mut out = self.clone();
        for (key, value) in other {
            match out.entry(key.clone()) {
                hash_map::Entry::Vacant(entry) => {
                    entry.insert(value.clone());
                }
                hash_map::Entry::Occupied(entry) => {
                    let current = entry.into_mut();
                    *current = current.meet(value);
                }
            }
        }
        out
    }
}

pub trait OrdMeet: Ord + Clone {}

impl<T: OrdMeet> Meet for T {
    fn meet(&self, other: &Self) -> Self {
        self.min(other).clone()
    }
}
