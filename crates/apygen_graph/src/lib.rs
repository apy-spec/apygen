use imbl::HashMap as ImmutableHashMap;
use imbl::HashSet as ImmutableHashSet;
use imbl::OrdMap;
use imbl::OrdSet;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::hash::Hash;

pub mod dot;
pub use imbl;

pub trait Edge {
    type Node;
    fn from(&self) -> &Self::Node;
    fn to(&self) -> &Self::Node;
}

impl<N> Edge for (N, N) {
    type Node = N;
    fn from(&self) -> &Self::Node {
        &self.0
    }
    fn to(&self) -> &Self::Node {
        &self.1
    }
}

pub trait Graph {
    type Node: Eq;
    type Edge: Edge<Node = Self::Node> + Eq;
    type NodeData;
    type EdgeData;

    fn nodes(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)>;
    fn edges(&self) -> impl Iterator<Item = (&Self::Edge, &Self::EdgeData)>;
    fn node_indices(&self) -> impl Iterator<Item = &Self::Node> {
        self.nodes().into_iter().map(|(node, _)| node)
    }
    fn edge_indices(&self) -> impl Iterator<Item = &Self::Edge> {
        self.edges().into_iter().map(|(edge, _)| edge)
    }
    fn get_node_data(&self, node: &Self::Node) -> Option<&Self::NodeData> {
        for (n, node_data) in self.nodes() {
            if n == node {
                return Some(node_data);
            }
        }
        None
    }
    fn get_edge_data(&self, edge: &Self::Edge) -> Option<&Self::EdgeData> {
        for (e, edge_data) in self.edges() {
            if e == edge {
                return Some(edge_data);
            }
        }
        None
    }
    fn successors(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
        self.edge_indices().filter_map(move |edge| {
            if edge.from() == node {
                Some(edge.to())
            } else {
                None
            }
        })
    }
    fn predecessors(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
        self.edge_indices().filter_map(move |edge| {
            if edge.to() == node {
                Some(edge.from())
            } else {
                None
            }
        })
    }
}

macro_rules! define_graph {
    (
        $graph:ident,
        $data:ident,
        $map:ident,
        $set:ident,
        bounds = ($($bounds:tt)*),
        derives = ($($derives:tt)*)
    ) => {
        #[derive(Default, Debug, Clone, PartialEq, Eq, $($derives)*)]
        struct $data<N: $($bounds)* + Clone, ND: Clone> {
            pub data: ND,
            pub successors: $set<N>,
            pub predecessors: $set<N>,
        }

        impl<N: $($bounds)* + Clone, ND: Clone> $data<N, ND> {
            pub fn new(data: ND) -> Self {
                Self {
                    data,
                    successors: $set::new(),
                    predecessors: $set::new(),
                }
            }
        }

        #[derive(Debug, Clone, PartialEq, Eq, $($derives)*)]
        pub struct $graph<N: $($bounds)* + Clone, ND: Clone, ED: Clone> {
            nodes: $map<N, $data<N, ND>>,
            edges: $map<(N, N), ED>,
        }

        impl<N: $($bounds)* + Clone, ND: Clone, ED: Clone> $graph<N, ND, ED> {
            pub fn new() -> Self {
                Self::default()
            }
            pub fn insert_node(&mut self, node: N, data: ND) -> Option<ND> {
                self.nodes
                    .insert(node, $data::new(data))
                    .map(|entry| entry.data)
            }
            pub fn get_mut_node_data(&mut self, node: &N) -> Option<&mut ND> {
                self.nodes.get_mut(node).map(|node_data| &mut node_data.data)
            }
            pub fn get_mut_or_default_node_data(&mut self, node: N) -> &mut ND
            where
                ND: Default,
            {
                &mut self
                    .nodes
                    .entry(node)
                    .or_insert($data::new(ND::default()))
                    .data
            }
            pub fn remove_node(&mut self, node: &N) -> Option<ND> {
                self.nodes.remove(node).map(|entry| entry.data)
            }
            pub fn insert_edge(&mut self, edge: (N, N), data: ED) -> Option<ED> {
                if !self.nodes.contains_key(edge.from()) || !self.nodes.contains_key(edge.to()) {
                    return None;
                }

                self.nodes
                    .get_mut(edge.from())
                    .expect("from node should exist")
                    .successors
                    .insert(edge.to().clone());
                self.nodes
                    .get_mut(edge.to())
                    .expect("to node should exist")
                    .predecessors
                    .insert(edge.from().clone());

                self.edges.insert(edge, data)
            }
            pub fn get_mut_edge_data(&mut self, edge: &(N, N)) -> Option<&mut ED> {
                self.edges.get_mut(edge)
            }
            pub fn get_mut_or_default_edge_data(&mut self, edge: (N, N)) -> Option<&mut ED>
            where
                ED: Default,
            {
                if !self.nodes.contains_key(edge.from()) || !self.nodes.contains_key(edge.to()) {
                    return None;
                }

                self.nodes
                    .get_mut(edge.from())
                    .expect("from node should exist")
                    .successors
                    .insert(edge.to().clone());
                self.nodes
                    .get_mut(edge.to())
                    .expect("to node should exist")
                    .predecessors
                    .insert(edge.from().clone());

                Some(self.edges.entry(edge).or_default())
            }
            pub fn remove_edge(&mut self, edge: &(N, N)) -> Option<ED> {
                let previous_edge_data = self.edges.remove(edge)?;

                self.nodes
                    .get_mut(edge.from())
                    .expect("from node should exist")
                    .successors
                    .remove(edge.to());
                self.nodes
                    .get_mut(edge.to())
                    .expect("to node should exist")
                    .predecessors
                    .remove(edge.from());

                Some(previous_edge_data)
            }
        }

        impl<N: $($bounds)* + Clone, ND: Clone, ED: Clone> Default for $graph<N, ND, ED> {
            fn default() -> Self {
                Self {
                    nodes: $map::default(),
                    edges: $map::default(),
                }
            }
        }

        impl<N: $($bounds)* + Clone, ND: Clone, ED: Clone> Graph for $graph<N, ND, ED> {
            type Node = N;
            type Edge = (N, N);
            type NodeData = ND;
            type EdgeData = ED;

            fn nodes(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)> {
                self.nodes
                    .iter()
                    .map(move |(node, entry)| (node, &entry.data))
            }
            fn edges(&self) -> impl Iterator<Item = (&Self::Edge, &Self::EdgeData)> {
                self.edges.iter()
            }
            fn node_indices(&self) -> impl Iterator<Item = &Self::Node> {
                self.nodes.keys()
            }
            fn edge_indices(&self) -> impl Iterator<Item = &Self::Edge> {
                self.edges.keys()
            }
            fn get_node_data(&self, node: &Self::Node) -> Option<&Self::NodeData> {
                self.nodes.get(node).map(|node_data| &node_data.data)
            }
            fn get_edge_data(&self, edge: &Self::Edge) -> Option<&Self::EdgeData> {
                self.edges.get(edge)
            }
            fn successors(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
                self.nodes
                    .get(node)
                    .into_iter()
                    .flat_map(|node_data| node_data.successors.iter())
            }
            fn predecessors(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
                self.nodes
                    .get(node)
                    .into_iter()
                    .flat_map(|node_data| node_data.predecessors.iter())
            }
        }

        impl<N: $($bounds)* + Clone + Display, ND: Clone + Display, ED: Clone + Display> dot::Dot for $graph<N, ND, ED> {
            fn fmt(&self, f: &mut Formatter<'_>, name: &str) -> std::fmt::Result {
                dot::fmt_digraph(f, &name, |f| {
                    for (node, node_data) in self.nodes() {
                        dot::fmt_display_labelled_node(f, node, node_data)?;
                    }
                    for (edge, edge_data) in self.edges() {
                        dot::fmt_display_labelled_edge(f, edge, edge_data)?;
                    }
                    Ok(())
                })
            }
        }
    };
}

define_graph!(
    BTreeGraph,
    BTreeGraphData,
    BTreeMap,
    BTreeSet,
    bounds = (Ord),
    derives = (PartialOrd, Ord, Hash)
);
define_graph!(
    HashGraph,
    HashGraphData,
    HashMap,
    HashSet,
    bounds = (Hash + Eq),
    derives = ()
);
define_graph!(
    OrdGraph,
    OrdGraphData,
    OrdMap,
    OrdSet,
    bounds = (Ord),
    derives = (PartialOrd, Ord, Hash)
);
define_graph!(
    ImmutableHashGraph,
    ImmutableHashGraphData,
    ImmutableHashMap,
    ImmutableHashSet,
    bounds = (Hash + Eq),
    derives = ()
);
