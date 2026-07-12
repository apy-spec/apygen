pub trait AbstractState {
    type Key;
    type AbstractValue;

    fn get(&self, key: &Self::Key) -> Option<&Self::AbstractValue>;
    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::AbstractValue>;
    fn get_or_insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue;
    fn insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> &mut Self::AbstractValue;
}

pub struct AbstractStateProxy<'a, S: AbstractState, P: AbstractState> {
    pub abstract_state: &'a S,
    pub proxy: P,
}

impl<
    'a,
    K: Clone,
    A: Clone,
    S: AbstractState<Key = K, AbstractValue = A>,
    P: AbstractState<Key = K, AbstractValue = A>,
> AbstractState for AbstractStateProxy<'a, S, P>
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
