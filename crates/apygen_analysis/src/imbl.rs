use crate::lattice::{Join, Meet};
pub use imbl;
use std::hash::Hash;

impl<T: Clone + Ord> Join for imbl::OrdSet<T> {
    fn join(&self, other: &Self) -> Self {
        self.clone().union(other.clone())
    }
}

impl<K: Clone + Ord, V: Join + Clone> Join for imbl::OrdMap<K, V> {
    fn join(&self, other: &Self) -> Self {
        self.clone()
            .union_with(other.clone(), |self_value, other_value| {
                self_value.join(&other_value)
            })
    }
}

impl<T: Clone + Eq + Hash> Join for imbl::HashSet<T> {
    fn join(&self, other: &Self) -> Self {
        self.clone().union(other.clone())
    }
}

impl<K: Clone + Eq + Hash, V: Join + Clone> Join for imbl::HashMap<K, V> {
    fn join(&self, other: &Self) -> Self {
        self.clone()
            .union_with(other.clone(), |self_value, other_value| {
                self_value.join(&other_value)
            })
    }
}

impl<T: Clone + Ord> Meet for imbl::OrdSet<T> {
    fn meet(&self, other: &Self) -> Self {
        self.clone().intersection(other.clone())
    }
}

impl<K: Clone + Ord, V: Meet + Clone> Meet for imbl::OrdMap<K, V> {
    fn meet(&self, other: &Self) -> Self {
        self.clone()
            .intersection_with(other.clone(), |self_value, other_value| {
                self_value.meet(&other_value)
            })
    }
}

impl<T: Clone + Eq + Hash> Meet for imbl::HashSet<T> {
    fn meet(&self, other: &Self) -> Self {
        self.clone().intersection(other.clone())
    }
}

impl<K: Clone + Eq + Hash, V: Meet + Clone> Meet for imbl::HashMap<K, V> {
    fn meet(&self, other: &Self) -> Self {
        self.clone()
            .intersection_with(other.clone(), |self_value, other_value| {
                self_value.meet(&other_value)
            })
    }
}
