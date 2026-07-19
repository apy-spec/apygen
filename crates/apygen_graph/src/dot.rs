use crate::{Edge, Graph};
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter};

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

pub trait DiGraphDot: Graph<Node: Ord, Edge: Ord> {
    fn fmt_node(
        &self,
        f: &mut Formatter<'_>,
        node: &Self::Node,
        node_data: &Self::NodeData,
    ) -> fmt::Result;
    fn fmt_edge(
        &self,
        f: &mut Formatter<'_>,
        edge: &Self::Edge,
        edge_data: &Self::EdgeData,
    ) -> fmt::Result;
}

impl<T: DiGraphDot> Dot for T {
    fn fmt(&self, f: &mut Formatter<'_>, name: &str) -> fmt::Result {
        let node_datas = self.node_data_iter().collect::<BTreeMap<_, _>>();
        let edge_datas = self.edge_data_iter().collect::<BTreeMap<_, _>>();

        write!(f, "digraph \"{}\" {{\n", name)?;
        for (node, data) in node_datas {
            self.fmt_node(f, node, data)?;
        }
        for (edge, edge_data) in edge_datas {
            self.fmt_edge(f, edge, edge_data)?;
        }
        f.write_str("}\n")
    }
}

pub trait DisplayDiGraphDot:
    DiGraphDot<
        Node: Display,
        NodeData: Display,
        Edge: Edge<Node = Self::Node> + Display,
        EdgeData: Display,
    >
{
    fn fmt_node(
        &self,
        f: &mut Formatter<'_>,
        node: &Self::Node,
        node_data: &Self::NodeData,
    ) -> fmt::Result {
        write!(
            f,
            "    \"{}\" [label=\"{}\"];\n",
            escape_dot(&node.to_string()),
            escape_dot(&node_data.to_string())
        )
    }
    fn fmt_edge(
        &self,
        f: &mut Formatter<'_>,
        edge: &Self::Edge,
        edge_data: &Self::EdgeData,
    ) -> fmt::Result {
        write!(
            f,
            "    \"{}\" -> \"{}\" [label=\"{}\"];\n",
            escape_dot(&edge.from().to_string()),
            escape_dot(&edge.to().to_string()),
            escape_dot(&edge_data.to_string())
        )
    }
}
