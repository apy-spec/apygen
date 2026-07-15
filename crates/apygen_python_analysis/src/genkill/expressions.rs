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

use crate::abstract_environment::{Completeness, Exception, Pureness, RaisedExceptions, Type};
use apygen_analysis::lattice::Join;
use std::fmt::Display;

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Join)]
pub struct PyEffects {
    pub exceptions: RaisedExceptions,
    pub pureness: Pureness,
    pub completeness: Completeness,
}

impl PyEffects {
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

    pub fn consume<T>(&mut self, eval: PyValueEval<T>) -> T {
        self.exceptions = self.exceptions.join(&eval.effects.exceptions);
        self.pureness = self.pureness.join(&eval.effects.pureness);
        self.completeness = self.completeness.join(&eval.effects.completeness);
        eval.value
    }
}

impl Display for PyEffects {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} - {} - {})",
            self.exceptions, self.pureness, self.completeness
        )
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Join)]
pub struct PyValueEval<T> {
    pub value: T,
    pub effects: PyEffects,
}

impl<T> PyValueEval<T> {
    pub fn new(value: T, effects: PyEffects) -> Self {
        PyValueEval { value, effects }
    }

    pub fn with_default_effects(value: T) -> Self {
        PyValueEval::new(value, PyEffects::default())
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> PyValueEval<U> {
        PyValueEval {
            value: f(self.value),
            effects: self.effects,
        }
    }

    pub fn extend_effects(mut self, effects: &PyEffects) -> Self {
        self.effects = self.effects.join(effects);
        self
    }
}

impl<T: Display> Display for PyValueEval<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ➤ {})", self.value, self.effects)
    }
}

pub type PyTypeEval = PyValueEval<Type>;

impl PyTypeEval {
    pub fn never() -> Self {
        PyTypeEval::new(Type::Never, PyEffects::default())
    }

    pub fn raise(exception: Exception) -> Self {
        PyTypeEval::new(
            Type::NoReturn,
            PyEffects {
                exceptions: RaisedExceptions::raise(exception),
                pureness: Pureness::Impure,
                completeness: Completeness::Partial,
            },
        )
    }

    pub fn unknown() -> Self {
        PyTypeEval::new(
            Type::Any,
            PyEffects {
                exceptions: RaisedExceptions::raise(Exception::any()),
                pureness: Pureness::Impure,
                completeness: Completeness::Partial,
            },
        )
    }
}

#[macro_export]
macro_rules! is_type_unreachable {
    ($ty:expr) => {
        matches!($ty, Type::Never | Type::NoReturn)
    };
}

#[macro_export]
macro_rules! pytype_return_unreachable {
    ($effects:expr, $ty:expr) => {
        if is_type_unreachable!($ty) {
            return PyTypeEval::new($ty, $effects);
        }
    };
}

#[macro_export]
macro_rules! pytype_consume_or_return {
    ($effects:expr, $eval:expr) => {{
        let ty = $effects.consume($eval);

        pytype_return_unreachable!($effects, ty);

        ty
    }};
}

#[macro_export]
macro_rules! pytype_consume_or_return_option {
    ($effects:expr, $eval:expr) => {{
        let ty = $effects.consume($eval);

        if is_type_unreachable!(ty) {
            return Some(PyTypeEval::new(ty, $effects));
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
