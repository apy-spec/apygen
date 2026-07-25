use std::fmt::Debug;

pub trait AbstractState {
    type Key;
    type AbstractValue;

    fn contains(&self, key: &Self::Key) -> bool {
        self.get(key).is_some()
    }
    fn get(&self, key: &Self::Key) -> Option<&Self::AbstractValue>;
    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::AbstractValue>;
    fn get_or_insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue;
    fn get_or_insert_default(&mut self, key: Self::Key) -> &mut Self::AbstractValue
    where
        Self::AbstractValue: Default,
    {
        self.get_or_insert(key, Self::AbstractValue::default())
    }
    fn get_clone(&self, key: &Self::Key) -> Option<Self::AbstractValue>
    where
        Self::AbstractValue: Clone,
    {
        self.get(key).cloned()
    }
    fn get_clone_or_else(
        &self,
        key: &Self::Key,
        f: &dyn Fn() -> Self::AbstractValue,
    ) -> Self::AbstractValue
    where
        Self::AbstractValue: Clone,
    {
        self.get_clone(key).unwrap_or_else(f)
    }
    fn get_clone_or_default(&self, key: &Self::Key) -> Self::AbstractValue
    where
        Self::AbstractValue: Default + Clone,
    {
        self.get_clone(key).unwrap_or_default()
    }
    fn insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue;
    fn extend(&mut self, iterator: &mut dyn Iterator<Item = (Self::Key, Self::AbstractValue)>) {
        for (key, abstract_value) in iterator {
            self.insert(key, abstract_value);
        }
    }
}

pub struct AbstractStateProxy<'a, K, A, P: AbstractState<Key = K, AbstractValue = A>> {
    pub abstract_state: &'a dyn AbstractState<Key = K, AbstractValue = A>,
    pub proxy: P,
}

impl<'a, K, A, P: AbstractState<Key = K, AbstractValue = A>> AbstractStateProxy<'a, K, A, P> {
    pub fn new(
        abstract_state: &'a dyn AbstractState<Key = K, AbstractValue = A>,
        proxy: P,
    ) -> Self {
        Self {
            abstract_state,
            proxy,
        }
    }
    pub fn with_default_proxy(
        abstract_state: &'a dyn AbstractState<Key = K, AbstractValue = A>,
    ) -> Self
    where
        P: Default,
    {
        Self::new(abstract_state, P::default())
    }
}

impl<'a, K, A, P: AbstractState<Key = K, AbstractValue = A> + PartialEq> PartialEq
    for AbstractStateProxy<'a, K, A, P>
{
    fn eq(&self, other: &Self) -> bool {
        std::ptr::addr_eq(self.abstract_state, other.abstract_state) && self.proxy == other.proxy
    }
}

impl<'a, K, A, P: AbstractState<Key = K, AbstractValue = A> + PartialEq> Eq
    for AbstractStateProxy<'a, K, A, P>
{
}

impl<'a, K, A, P: AbstractState<Key = K, AbstractValue = A> + Clone> Clone
    for AbstractStateProxy<'_, K, A, P>
{
    fn clone(&self) -> Self {
        Self::new(self.abstract_state, self.proxy.clone())
    }
}

impl<'a, K, A, P: AbstractState<Key = K, AbstractValue = A> + Debug> Debug
    for AbstractStateProxy<'a, K, A, P>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AbstractStateProxy")
            .field(
                "abstract_state",
                &(self.abstract_state as *const dyn AbstractState<Key = K, AbstractValue = A>),
            )
            .field("proxy", &self.proxy)
            .finish()
    }
}

impl<K: Clone, A: Clone, P: AbstractState<Key = K, AbstractValue = A>> AbstractState
    for AbstractStateProxy<'_, K, A, P>
{
    type Key = K;
    type AbstractValue = A;

    fn get(&self, key: &Self::Key) -> Option<&Self::AbstractValue> {
        self.proxy.get(key).or_else(|| self.abstract_state.get(key))
    }

    fn get_mut(&mut self, key: &K) -> Option<&mut A> {
        if let Some(abstract_value) = self.abstract_state.get(key) {
            Some(
                self.proxy
                    .get_or_insert(key.clone(), abstract_value.clone()),
            )
        } else {
            self.proxy.get_mut(key)
        }
    }

    fn get_or_insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue {
        let new_abstract_value = self
            .abstract_state
            .get(&key)
            .cloned()
            .unwrap_or(abstract_value);
        self.proxy.get_or_insert(key, new_abstract_value)
    }

    fn insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue {
        self.proxy.insert(key, abstract_value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn test_abstract_state_dyn_compatibility(
        _: Box<dyn AbstractState<Key = String, AbstractValue = i32>>,
    ) {
    }
}
