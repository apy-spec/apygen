pub trait AbstractState<'a> {
    type Key;
    type AbstractValue;

    fn get(&self, key: &Self::Key) -> Option<&'a Self::AbstractValue>;
    fn get_mut(&mut self, key: &Self::Key) -> Option<&'a mut Self::AbstractValue>;
    fn insert(
        &mut self,
        key: Self::Key,
        abstract_value: Self::AbstractValue,
    ) -> Option<&'a mut Self::AbstractValue>;
}

pub struct AbstractStateProxy<'a, S: AbstractState<'a>, P: AbstractState<'a>> {
    pub abstract_state: &'a S,
    pub proxy: P,
}

impl<
    'a,
    K: Clone,
    A: Clone,
    S: AbstractState<'a, Key = K, AbstractValue = A>,
    P: AbstractState<'a, Key = K, AbstractValue = A>,
> AbstractState<'a> for AbstractStateProxy<'a, S, P>
{
    type Key = K;
    type AbstractValue = A;

    fn get(&self, key: &Self::Key) -> Option<&'a Self::AbstractValue> {
        self.proxy.get(key).or_else(|| self.abstract_state.get(key))
    }

    fn get_mut(&mut self, key: &K) -> Option<&'a mut A> {
        if let Some(value) = self.proxy.get_mut(key) {
            Some(value)
        } else {
            self.proxy
                .insert(key.clone(), self.abstract_state.get(key)?.clone())
        }
    }

    fn insert(&mut self, key: K, value: A) -> Option<&'a mut A> {
        self.proxy.insert(key, value)
    }
}
