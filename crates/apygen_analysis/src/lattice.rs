use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, btree_map, hash_map};
use std::hash::Hash;
use std::sync::Arc;

pub trait LatticeOrd {
    fn leq(&self, other: &Self) -> bool;
}

pub trait ContextualLatticeOrd<C, E> {
    fn leq(&self, other: &Self, context: &C) -> Result<bool, E>;
}

impl<T: LatticeOrd, C, E> ContextualLatticeOrd<C, E> for T {
    fn leq(&self, other: &Self, _context: &C) -> Result<bool, E> {
        Ok(self.leq(other))
    }
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

pub trait ContextualJoin<C, E>
where
    Self: Sized,
{
    fn join(&self, other: &Self, context: &C) -> Result<Self, E>;
}

impl<T: Join, C, E> ContextualJoin<C, E> for T {
    fn join(&self, other: &Self, _context: &C) -> Result<Self, E> {
        Ok(self.join(other))
    }
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

pub trait ContextualMeet<C, E>
where
    Self: Sized,
{
    fn meet(&self, other: &Self, context: &C) -> Result<Self, E>;
}

impl<T: Meet, C, E> ContextualMeet<C, E> for T {
    fn meet(&self, other: &Self, _context: &C) -> Result<Self, E> {
        Ok(self.meet(other))
    }
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

pub use apygen_analysis_derive::Join;
pub use apygen_analysis_derive::LatticeOrd;
pub use apygen_analysis_derive::Meet;
