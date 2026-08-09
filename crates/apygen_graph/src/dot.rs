use crate::Edge;
use std::fmt::{self, Display, Formatter};

pub fn escape_dot(string: &str) -> String {
    string.replace('"', "&quot;").replace("\\", "\\\\")
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

impl<'a, T: Dot> Display for ToDotDisplay<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        T::fmt(self.dot, f, self.name)
    }
}

impl<T: Dot> ToDot for T {
    fn dot(&self, name: &str) -> String {
        ToDotDisplay { name, dot: self }.to_string()
    }
}

pub fn fmt_digraph(
    f: &mut Formatter<'_>,
    name: &impl Display,
    fmt_lines: impl Fn(&mut Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    write!(f, "digraph \"{}\" {{\n", name)?;
    fmt_lines(f)?;
    f.write_str("}\n")
}

pub fn fmt_node(
    f: &mut Formatter<'_>,
    fmt_node: impl Fn(&mut Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    f.write_str("    \"")?;
    fmt_node(f)?;
    f.write_str("\";\n")
}

pub fn fmt_labelled_node(
    f: &mut Formatter<'_>,
    fmt_node: impl Fn(&mut Formatter<'_>) -> fmt::Result,
    fmt_label: impl Fn(&mut Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    f.write_str("    \"")?;
    fmt_node(f)?;
    f.write_str("\" [label=\"")?;
    fmt_label(f)?;
    f.write_str("\"];\n")
}

pub fn fmt_display_node(f: &mut Formatter<'_>, node: &impl Display) -> fmt::Result {
    fmt_node(f, |f| Display::fmt(&escape_dot(&node.to_string()), f))
}

pub fn fmt_display_labelled_node(
    f: &mut Formatter<'_>,
    node: &impl Display,
    label: &impl Display,
) -> fmt::Result {
    fmt_labelled_node(
        f,
        |f| Display::fmt(&escape_dot(&node.to_string()), f),
        |f| Display::fmt(&escape_dot(&label.to_string()), f),
    )
}

pub fn fmt_edge(
    f: &mut Formatter<'_>,
    fmt_from: impl Fn(&mut Formatter<'_>) -> fmt::Result,
    fmt_to: impl Fn(&mut Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    f.write_str("    \"")?;
    fmt_from(f)?;
    f.write_str("\" -> \"")?;
    fmt_to(f)?;
    f.write_str("\";\n")
}

pub fn fmt_labelled_edge(
    f: &mut Formatter<'_>,
    fmt_from: impl Fn(&mut Formatter<'_>) -> fmt::Result,
    fmt_to: impl Fn(&mut Formatter<'_>) -> fmt::Result,
    fmt_label: impl Fn(&mut Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    f.write_str("    \"")?;
    fmt_from(f)?;
    f.write_str("\" -> \"")?;
    fmt_to(f)?;
    f.write_str("\" [label=\"")?;
    fmt_label(f)?;
    f.write_str("\"];\n")
}

pub fn fmt_display_edge<'e>(
    f: &mut Formatter<'_>,
    edge: impl Edge<'e, Node = impl Display + 'e>,
) -> fmt::Result {
    fmt_edge(
        f,
        |f| Display::fmt(&escape_dot(&edge.from().to_string()), f),
        |f| Display::fmt(&escape_dot(&edge.to().to_string()), f),
    )
}

pub fn fmt_display_labelled_edge<'e>(
    f: &mut Formatter<'_>,
    edge: impl Edge<'e, Node = impl Display + 'e>,
    label: &impl Display,
) -> fmt::Result {
    fmt_labelled_edge(
        f,
        |f| Display::fmt(&escape_dot(&edge.from().to_string()), f),
        |f| Display::fmt(&escape_dot(&edge.to().to_string()), f),
        |f| Display::fmt(&escape_dot(&label.to_string()), f),
    )
}
