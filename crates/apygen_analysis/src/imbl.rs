use crate::lattice::{Join, LatticeOrd, Meet};
pub use imbl;
use std::hash::Hash;

impl<T: Ord> LatticeOrd for imbl::OrdSet<T> {
    fn leq(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<K: Ord, V: LatticeOrd> LatticeOrd for imbl::OrdMap<K, V> {
    fn leq(&self, other: &Self) -> bool {
        self.is_submap_by(other, |self_value, other_value| self_value.leq(other_value))
    }
}

impl<T: Eq + Hash> LatticeOrd for imbl::HashSet<T> {
    fn leq(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<K: Eq + Hash, V: LatticeOrd> LatticeOrd for imbl::HashMap<K, V> {
    fn leq(&self, other: &Self) -> bool {
        self.is_submap_by(other, |self_value, other_value| self_value.leq(other_value))
    }
}

impl<T: Clone + Ord> Join for imbl::OrdSet<T> {
    fn join(&self, other: &Self) -> Self {
        if self.ptr_eq(other) || self == other {
            self.clone()
        } else {
            self.clone().union(other.clone())
        }
    }
}

impl<K: Clone + Ord, V: Join + Clone + Eq> Join for imbl::OrdMap<K, V> {
    fn join(&self, other: &Self) -> Self {
        if self.ptr_eq(other) || self == other {
            self.clone()
        } else {
            self.clone()
                .union_with(other.clone(), |self_value, other_value| {
                    self_value.join(&other_value)
                })
        }
    }
}

impl<T: Clone + Eq + Hash> Join for imbl::HashSet<T> {
    fn join(&self, other: &Self) -> Self {
        if self.ptr_eq(other) || self == other {
            self.clone()
        } else {
            self.clone().union(other.clone())
        }
    }
}

impl<K: Clone + Eq + Hash, V: Join + Clone + Eq> Join for imbl::HashMap<K, V> {
    fn join(&self, other: &Self) -> Self {
        if self.ptr_eq(other) || self == other {
            self.clone()
        } else {
            self.clone()
                .union_with(other.clone(), |self_value, other_value| {
                    self_value.join(&other_value)
                })
        }
    }
}

impl<T: Clone + Ord> Meet for imbl::OrdSet<T> {
    fn meet(&self, other: &Self) -> Self {
        if self.ptr_eq(other) || self == other {
            self.clone()
        } else {
            self.clone().union(other.clone())
        }
    }
}

impl<K: Clone + Ord, V: Meet + Clone + Eq> Meet for imbl::OrdMap<K, V> {
    fn meet(&self, other: &Self) -> Self {
        if self.ptr_eq(other) || self == other {
            self.clone()
        } else {
            self.clone()
                .intersection_with(other.clone(), |self_value, other_value| {
                    self_value.meet(&other_value)
                })
        }
    }
}

impl<T: Clone + Eq + Hash> Meet for imbl::HashSet<T> {
    fn meet(&self, other: &Self) -> Self {
        if self.ptr_eq(other) || self == other {
            self.clone()
        } else {
            self.clone().intersection(other.clone())
        }
    }
}

impl<K: Clone + Eq + Hash, V: Meet + Clone + Eq> Meet for imbl::HashMap<K, V> {
    fn meet(&self, other: &Self) -> Self {
        if self.ptr_eq(other) || self == other {
            self.clone()
        } else {
            self.clone()
                .intersection_with(other.clone(), |self_value, other_value| {
                    self_value.meet(&other_value)
                })
        }
    }
}
