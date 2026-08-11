use crate::constraint_graph::graph::imbl::hashmap as immutable_hashmap;
use crate::constraint_graph::graph::{
    Graph, GraphData, GraphMut, ImmutableHashGraph, ImmutableHashGraphData,
};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::hash::Hash;

pub trait DependentGraph: Sync {
    type Node;
    type NodeData;
    type EdgeData;

    fn get_node_data<'a: 'n, 'n>(&'a self, node: &'n Self::Node) -> Option<&'a Self::NodeData>;
    fn get_edge_data<'a: 'n, 'n>(
        &'a self,
        from: &'n Self::Node,
        to: &'n Self::Node,
    ) -> Option<&'a Self::EdgeData>;
    fn insert_node(&mut self, node: Self::Node, node_data: Self::NodeData) -> &mut Self::NodeData;
    fn get_or_insert_node(
        &mut self,
        node: Self::Node,
        f: &dyn Fn() -> Self::NodeData,
    ) -> &mut Self::NodeData;
    fn insert_edge(
        &mut self,
        from: Self::Node,
        to: Self::Node,
        edge_data: Self::EdgeData,
    ) -> Option<&mut Self::EdgeData>;
    fn get_or_insert_edge(
        &mut self,
        from: Self::Node,
        to: Self::Node,
        f: &dyn Fn() -> Self::EdgeData,
    ) -> Option<&mut Self::EdgeData>;
    fn dependents<'a>(
        &'a self,
        node: &'a Self::Node,
    ) -> Box<dyn Iterator<Item = &'a Self::Node> + 'a>;
}

#[derive(Clone)]
pub struct DependentGraphProxy<'a, N: Hash + Eq + Clone, ND: Clone, ED: Clone> {
    pub graph: &'a dyn DependentGraph<Node = N, NodeData = ND, EdgeData = ED>,
    pub nodes: HashMap<N, ND>,
    pub dependents: HashMap<N, HashMap<N, Option<ED>>>,
}

impl<'a, N: Hash + Eq + Clone, ND: Clone, ED: Clone> DependentGraphProxy<'a, N, ND, ED> {
    pub fn with_default_proxy(
        graph: &'a dyn DependentGraph<Node = N, NodeData = ND, EdgeData = ED>,
    ) -> Self {
        Self {
            graph,
            nodes: HashMap::new(),
            dependents: HashMap::new(),
        }
    }
}

impl<N: Hash + Eq + Sync + Clone, ND: Sync + Clone, ED: Sync + Clone> DependentGraph
    for DependentGraphProxy<'_, N, ND, ED>
{
    type Node = N;
    type NodeData = ND;
    type EdgeData = ED;

    fn get_node_data<'a: 'n, 'n>(&'a self, node: &'n Self::Node) -> Option<&'a Self::NodeData> {
        if let Some(node_data) = self.nodes.get(node) {
            Some(node_data)
        } else {
            self.graph.get_node_data(node)
        }
    }
    fn get_edge_data<'a: 'n, 'n>(
        &'a self,
        from: &'n Self::Node,
        to: &'n Self::Node,
    ) -> Option<&'a Self::EdgeData> {
        if let Some(tos) = self.dependents.get(from) {
            tos.get(to).and_then(|edge_data| {
                edge_data
                    .as_ref()
                    .or_else(|| self.graph.get_edge_data(from, to))
            })
        } else {
            self.graph.get_edge_data(from, to)
        }
    }
    fn insert_node(&mut self, node: Self::Node, node_data: Self::NodeData) -> &mut Self::NodeData {
        self.nodes.entry(node).insert_entry(node_data).into_mut()
    }
    fn get_or_insert_node(
        &mut self,
        node: Self::Node,
        f: &dyn Fn() -> Self::NodeData,
    ) -> &mut Self::NodeData {
        let node_data = self.graph.get_node_data(&node).cloned().unwrap_or_else(f);
        self.nodes.entry(node).or_insert(node_data)
    }
    fn insert_edge(
        &mut self,
        from: Self::Node,
        to: Self::Node,
        edge_data: Self::EdgeData,
    ) -> Option<&mut Self::EdgeData> {
        if self.get_node_data(&from).is_none() || self.get_node_data(&to).is_none() {
            return None;
        }
        Some(
            self.dependents
                .entry(from.clone())
                .or_insert_with(|| {
                    self.graph
                        .dependents(&from)
                        .map(|to| (to.clone(), None))
                        .collect()
                })
                .entry(to)
                .insert_entry(Some(edge_data))
                .into_mut()
                .as_mut()
                .expect("edge data should exist"),
        )
    }
    fn get_or_insert_edge(
        &mut self,
        from: Self::Node,
        to: Self::Node,
        f: &dyn Fn() -> Self::EdgeData,
    ) -> Option<&mut Self::EdgeData> {
        if self.get_node_data(&from).is_none() || self.get_node_data(&to).is_none() {
            return None;
        }

        let node_data = self
            .graph
            .get_edge_data(&from, &to)
            .cloned()
            .unwrap_or_else(f);

        Some(
            match self
                .dependents
                .entry(from.clone())
                .or_insert_with(|| {
                    self.graph
                        .dependents(&from)
                        .map(|to| (to.clone(), None))
                        .collect()
                })
                .entry(to.clone())
            {
                Entry::Occupied(entry) => {
                    let current = entry.into_mut();
                    if current.is_none() {
                        *current = Some(node_data);
                    }
                    current
                }
                Entry::Vacant(entry) => entry.insert(Some(node_data)),
            }
            .as_mut()
            .expect("edge data should exist"),
        )
    }
    fn dependents<'a>(
        &'a self,
        node: &'a Self::Node,
    ) -> Box<dyn Iterator<Item = &'a Self::Node> + 'a> {
        if let Some(tos) = self.dependents.get(node) {
            Box::new(tos.keys())
        } else {
            Box::new(self.graph.dependents(node))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImmutableHashDependentGraph<
    N: Hash + Eq,
    ND,
    ED,
    GD: GraphData<Node = N, NodeData = ND> = ImmutableHashGraphData<N, ND>,
> {
    pub graph: ImmutableHashGraph<N, ND, ED, GD>,
}

impl<
    N: Hash + Eq + Clone + Send + Sync,
    ND: Clone,
    ED: Clone + Send + Sync,
    GD: GraphData<Node = N, NodeData = ND> + Clone + Send + Sync,
> DependentGraph for ImmutableHashDependentGraph<N, ND, ED, GD>
{
    type Node = N;
    type NodeData = ND;
    type EdgeData = ED;

    fn get_node_data<'a: 'n, 'n>(&'a self, node: &'n Self::Node) -> Option<&'a Self::NodeData> {
        self.graph.get_node_data(node)
    }
    fn get_edge_data<'a: 'n, 'n>(
        &'a self,
        from: &'n Self::Node,
        to: &'n Self::Node,
    ) -> Option<&'a Self::EdgeData> {
        self.graph.get_edge_data(&(from.clone(), to.clone()))
    }
    fn insert_node(&mut self, node: Self::Node, node_data: Self::NodeData) -> &mut Self::NodeData {
        self.graph.insert_node(node, node_data)
    }
    fn get_or_insert_node(
        &mut self,
        node: Self::Node,
        f: &dyn Fn() -> Self::NodeData,
    ) -> &mut Self::NodeData {
        self.graph.get_or_insert_node(node, f)
    }
    fn insert_edge(
        &mut self,
        from: Self::Node,
        to: Self::Node,
        edge_data: Self::EdgeData,
    ) -> Option<&mut Self::EdgeData> {
        match self.graph.get_edge_entry((from, to))? {
            immutable_hashmap::Entry::Occupied(entry) => {
                let current = entry.into_mut();
                *current = edge_data;
                Some(current)
            }
            immutable_hashmap::Entry::Vacant(entry) => Some(entry.insert(edge_data)),
        }
    }
    fn get_or_insert_edge(
        &mut self,
        from: Self::Node,
        to: Self::Node,
        f: &dyn Fn() -> Self::EdgeData,
    ) -> Option<&mut Self::EdgeData> {
        Some(self.graph.get_edge_entry((from, to))?.or_insert_with(f))
    }
    fn dependents<'a>(
        &'a self,
        node: &'a Self::Node,
    ) -> Box<dyn Iterator<Item = &'a Self::Node> + 'a> {
        Box::new(self.graph.successors(node))
    }
}

impl<N: Hash + Eq + Clone, ND: Clone, ED: Clone, GD: GraphData<Node = N, NodeData = ND> + Clone>
    Default for ImmutableHashDependentGraph<N, ND, ED, GD>
{
    fn default() -> Self {
        Self {
            graph: ImmutableHashGraph::default(),
        }
    }
}
