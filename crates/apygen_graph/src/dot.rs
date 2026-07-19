use std::fmt::{self, Formatter};

pub fn escape_dot(string: &str) -> String {
    string.replace('"', r#"\""#)
}

pub trait Dot {
    fn fmt(&self, f: &mut Formatter<'_>, name: &str) -> fmt::Result;
}

pub trait ToDot {
    fn dot(&self, name: &str) -> String;
}

struct ToDotDisplay<'a, T> {
    name: &'a str,
    dot: &'a T,
}

impl<'a, T: Dot> fmt::Display for ToDotDisplay<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        T::fmt(self.dot, f, self.name)
    }
}

impl<T: Dot> ToDot for T {
    fn dot(&self, name: &str) -> String {
        ToDotDisplay { name, dot: self }.to_string()
    }
}
