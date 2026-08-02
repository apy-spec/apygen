use crate::EvaluationState;
use crate::analysis::abstract_state::AbstractState;
use crate::analysis::lattice::Join;
use crate::calls::Arguments;
use crate::identifiers::Namespace;
use crate::inference::{Completeness, Exception, Pureness, RaisedExceptions, Sourced, Type};
use std::fmt::Display;
use std::sync::Arc;

pub mod literal_boolean;
pub mod literal_bytes;
pub mod literal_class;
pub mod literal_complex;
pub mod literal_ellipsis;
pub mod literal_float;
pub mod literal_integer;
pub mod literal_none;
pub mod literal_string;
pub mod type_literal;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Call<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> {
    pub target: Arc<Namespace>,
    pub context: S,
    pub arguments: Arguments,
}

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Call<S> {
    pub fn new(target: Arc<Namespace>, context: S, arguments: Arguments) -> Self {
        Self {
            target,
            context,
            arguments,
        }
    }
}

#[derive(Clone, Join)]
pub struct PyEffects<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> {
    pub exceptions: RaisedExceptions,
    pub pureness: Pureness,
    pub completeness: Completeness,
    pub calls: imbl::OrdSet<Call<S>>,
}

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> PyEffects<S> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_exceptions(mut self, exceptions: RaisedExceptions) -> Self {
        self.exceptions = exceptions;
        self
    }

    pub fn with_pureness(mut self, pureness: Pureness) -> Self {
        self.pureness = pureness;
        self
    }

    pub fn with_completeness(mut self, completeness: Completeness) -> Self {
        self.completeness = completeness;
        self
    }

    pub fn with_calls(mut self, calls: imbl::OrdSet<Call<S>>) -> Self {
        self.calls = calls;
        self
    }

    pub fn consume<T>(&mut self, eval: PyValueEval<T, S>) -> T
    where
        S: Clone + Ord,
    {
        self.exceptions = self.exceptions.join(&eval.effects.exceptions);
        self.pureness = self.pureness.join(&eval.effects.pureness);
        self.completeness = self.completeness.join(&eval.effects.completeness);
        self.calls = self.calls.join(&eval.effects.calls);
        eval.value
    }
}

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Default for PyEffects<S> {
    fn default() -> Self {
        Self {
            exceptions: Default::default(),
            pureness: Default::default(),
            completeness: Default::default(),
            calls: Default::default(),
        }
    }
}

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Display for PyEffects<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} - {} - {})",
            self.exceptions, self.pureness, self.completeness
        )
    }
}

#[derive(Clone, Join)]
pub struct PyValueEval<T, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> {
    pub value: T,
    pub effects: PyEffects<S>,
}

impl<T, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> PyValueEval<T, S> {
    pub fn new(value: T, effects: PyEffects<S>) -> Self {
        PyValueEval { value, effects }
    }

    pub fn with_default_effects(value: T) -> Self {
        PyValueEval::new(value, PyEffects::default())
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> PyValueEval<U, S> {
        PyValueEval {
            value: f(self.value),
            effects: self.effects,
        }
    }

    pub fn extend_effects(mut self, effects: &PyEffects<S>) -> Self
    where
        S: Clone + Ord,
    {
        self.effects = self.effects.join(effects);
        self
    }
}

impl<T: Default, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Default
    for PyValueEval<T, S>
{
    fn default() -> Self {
        Self::new(Default::default(), Default::default())
    }
}

impl<T: Display, S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> Display
    for PyValueEval<T, S>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ➤ {})", self.value, self.effects)
    }
}

pub type PyTypeEval<S> = PyValueEval<Sourced<Type>, S>;

impl<S: AbstractState<Key = Namespace, AbstractValue = EvaluationState>> PyTypeEval<S> {
    pub fn never() -> Self {
        PyTypeEval::with_default_effects(Sourced::inferred(Type::Never))
    }

    pub fn raise(exception: Exception) -> Self {
        PyTypeEval::new(
            Sourced::inferred(Type::NoReturn),
            PyEffects::new().with_exceptions(RaisedExceptions::raise(exception)),
        )
    }

    pub fn unknown() -> Self {
        PyTypeEval::new(
            Sourced::inferred(Type::Any),
            PyEffects::new()
                .with_exceptions(RaisedExceptions::raise(Exception::any()))
                .with_pureness(Pureness::Impure)
                .with_completeness(Completeness::Partial),
        )
    }
}

#[macro_export]
macro_rules! is_sourced_type_unreachable {
    ($ty:expr) => {
        matches!($ty.data, Type::Never | Type::NoReturn)
    };
}

#[macro_export]
macro_rules! pytype_consume_or_return_ok {
    ($effects:expr, $eval:expr) => {{
        let ty = $effects.consume($eval);

        if is_sourced_type_unreachable!(ty) {
            return Ok(PyTypeEval::new(ty, $effects));
        }

        ty
    }};
}

pub fn gen_bool_value(ty: &Type) -> Option<bool> {
    match ty {
        Type::Any => None,
        Type::Never => None,
        Type::NoReturn => None,
        Type::Instance(_) => None,
        Type::Union(_) => None,
        Type::Intersection(_) => None,
        Type::Literal(literal_value) => type_literal::as_boolean(literal_value.as_ref()),
    }
}
