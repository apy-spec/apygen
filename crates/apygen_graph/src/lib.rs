use imbl::{
    HashMap as ImmutableHashMap, HashSet as ImmutableHashSet, OrdMap, OrdSet,
    hashmap as immutable_hashmap, ordmap, shared_ptr::DefaultSharedPtr,
};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, btree_map, hash_map};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, RandomState};

pub use imbl;
pub mod dot;

pub trait GraphData {
    type Node;
    type NodeData;

    fn new(data: Self::NodeData) -> Self;
    fn data(&self) -> &Self::NodeData;
    fn data_mut(&mut self) -> &mut Self::NodeData;
    fn into_data(self) -> Self::NodeData;
    fn add_successor(&mut self, node: Self::Node);
    fn remove_successor(&mut self, node: &Self::Node);
    fn successors(&self) -> impl Iterator<Item = &Self::Node>;
    fn add_predecessor(&mut self, node: Self::Node);
    fn remove_predecessor(&mut self, node: &Self::Node);
    fn predecessors(&self) -> impl Iterator<Item = &Self::Node>;
}

macro_rules! impl_graph_data {
    ($node:ty, $node_data:ty) => {
        type Node = $node;
        type NodeData = $node_data;

        fn new(data: Self::NodeData) -> Self {
            Self {
                data,
                successors: Default::default(),
                predecessors: Default::default(),
            }
        }
        fn data(&self) -> &Self::NodeData {
            &self.data
        }
        fn data_mut(&mut self) -> &mut Self::NodeData {
            &mut self.data
        }
        fn into_data(self) -> Self::NodeData {
            self.data
        }
        fn add_successor(&mut self, node: Self::Node) {
            self.successors.insert(node);
        }
        fn remove_successor(&mut self, node: &Self::Node) {
            self.successors.remove(node);
        }
        fn successors(&self) -> impl Iterator<Item = &Self::Node> {
            self.successors.iter()
        }
        fn add_predecessor(&mut self, node: Self::Node) {
            self.predecessors.insert(node);
        }
        fn remove_predecessor(&mut self, node: &Self::Node) {
            self.predecessors.remove(node);
        }
        fn predecessors(&self) -> impl Iterator<Item = &Self::Node> {
            self.predecessors.iter()
        }
    };
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BTreeGraphData<N: Ord, ND> {
    pub data: ND,
    pub successors: BTreeSet<N>,
    pub predecessors: BTreeSet<N>,
}

impl<N: Ord, ND> GraphData for BTreeGraphData<N, ND> {
    impl_graph_data!(N, ND);
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct HashGraphData<N: Hash + Eq, ND> {
    pub data: ND,
    pub successors: HashSet<N>,
    pub predecessors: HashSet<N>,
}

impl<N: Hash + Eq, ND> GraphData for HashGraphData<N, ND> {
    impl_graph_data!(N, ND);
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OrdGraphData<N: Ord + Clone, ND> {
    pub data: ND,
    pub successors: OrdSet<N>,
    pub predecessors: OrdSet<N>,
}

impl<N: Ord + Clone, ND> GraphData for OrdGraphData<N, ND> {
    impl_graph_data!(N, ND);
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ImmutableHashGraphData<N: Hash + Eq + Clone, ND> {
    pub data: ND,
    pub successors: ImmutableHashSet<N>,
    pub predecessors: ImmutableHashSet<N>,
}

impl<N: Hash + Eq + Clone, ND> GraphData for ImmutableHashGraphData<N, ND> {
    impl_graph_data!(N, ND);
}

pub trait EdgeRef<'n> {
    type Node;
    fn from(&self) -> &'n Self::Node;
    fn to(&self) -> &'n Self::Node;
}

impl<'n, N> EdgeRef<'n> for (&'n N, &'n N) {
    type Node = N;
    fn from(&self) -> &'n Self::Node {
        self.0
    }
    fn to(&self) -> &'n Self::Node {
        self.1
    }
}

impl<'n, N> EdgeRef<'n> for &'n (N, N) {
    type Node = N;
    fn from(&self) -> &'n Self::Node {
        &self.0
    }
    fn to(&self) -> &'n Self::Node {
        &self.1
    }
}

pub trait Graph {
    type Node: Eq;
    type EdgeRef<'n>: EdgeRef<'n, Node = Self::Node>
    where
        Self: 'n;
    type NodeData;
    type EdgeData;

    fn nodes(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)>;
    fn edges(&self) -> impl Iterator<Item = (Self::EdgeRef<'_>, &Self::EdgeData)>;
    fn node_indices(&self) -> impl Iterator<Item = &Self::Node> {
        self.nodes().into_iter().map(|(node, _)| node)
    }
    fn edge_indices(&self) -> impl Iterator<Item = Self::EdgeRef<'_>> {
        self.edges().into_iter().map(|(edge, _)| edge)
    }
    fn get_node_data<'a: 'n, 'n>(&'a self, node: &'n Self::Node) -> Option<&'a Self::NodeData> {
        for (n, node_data) in self.nodes() {
            if n == node {
                return Some(node_data);
            }
        }
        None
    }
    fn get_edge_data<'a: 'n, 'n>(&'a self, edge: Self::EdgeRef<'n>) -> Option<&'a Self::EdgeData> {
        for (e, edge_data) in self.edges() {
            if e.from() == edge.from() && e.to() == edge.to() {
                return Some(edge_data);
            }
        }
        None
    }
    fn successors<'a: 'n, 'n>(
        &'a self,
        node: &'n Self::Node,
    ) -> impl Iterator<Item = &'a Self::Node> {
        self.edge_indices().filter_map(move |edge| {
            if edge.from() == node {
                Some(edge.to())
            } else {
                None
            }
        })
    }
    fn predecessors<'a: 'n, 'n>(
        &'a self,
        node: &'n Self::Node,
    ) -> impl Iterator<Item = &'a Self::Node> {
        self.edge_indices().filter_map(move |edge| {
            if edge.to() == node {
                Some(edge.from())
            } else {
                None
            }
        })
    }
}

pub trait GraphMut: Graph {
    type Edge;
    type EdgeEntry<'n>
    where
        Self: 'n;

    fn insert_node(&mut self, node: Self::Node, data: Self::NodeData) -> &mut Self::NodeData;
    fn get_or_insert_node(
        &mut self,
        node: Self::Node,
        f: impl FnOnce() -> Self::NodeData,
    ) -> &mut Self::NodeData;
    fn get_or_insert_default_node(&mut self, node: Self::Node) -> &mut Self::NodeData
    where
        Self::NodeData: Default,
    {
        self.get_or_insert_node(node, Default::default)
    }
    fn get_mut_node_data(&mut self, node: &Self::Node) -> Option<&mut Self::NodeData>;
    fn remove_node(&mut self, node: &Self::Node) -> Option<Self::NodeData>;
    fn get_edge_entry(&mut self, edge: Self::Edge) -> Option<Self::EdgeEntry<'_>>;
    fn edge_entry(&mut self, edge: Self::Edge) -> Self::EdgeEntry<'_> {
        self.get_edge_entry(edge)
            .expect("edge should exist before getting edge entry")
    }
    fn get_mut_edge_data<'a: 'n, 'n>(
        &'a mut self,
        edge: Self::EdgeRef<'n>,
    ) -> Option<&'a mut Self::EdgeData>;
    fn remove_edge<'a: 'n, 'n>(&'a mut self, edge: Self::EdgeRef<'n>) -> Option<Self::EdgeData>;
}

macro_rules! impl_graph_methods {
    ($node:ty, $graph_data:ty) => {
        pub fn new() -> Self {
            Self {
                nodes: Default::default(),
                edges: Default::default(),
            }
        }
        fn mut_graph_data<'a: 'n, 'n>(&'a mut self, node: &'n $node) -> &'a mut $graph_data {
            self.nodes.get_mut(node).expect("node should exist")
        }
    };
}

macro_rules! impl_graph_default {
    () => {
        fn default() -> Self {
            Self::new()
        }
    };
}

macro_rules! impl_graph {
    ($node:ty, $node_data:ty, $edge_data:ty) => {
        type Node = $node;
        type EdgeRef<'n>
            = &'n (Self::Node, Self::Node)
        where
            Self: 'n;
        type NodeData = $node_data;
        type EdgeData = $edge_data;

        fn nodes(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)> {
            self.nodes
                .iter()
                .map(move |(node, graph_data)| (node, graph_data.data()))
        }
        fn edges(&self) -> impl Iterator<Item = (Self::EdgeRef<'_>, &Self::EdgeData)> {
            self.edges.iter()
        }
        fn node_indices(&self) -> impl Iterator<Item = &Self::Node> {
            self.nodes.keys()
        }
        fn edge_indices(&self) -> impl Iterator<Item = Self::EdgeRef<'_>> {
            self.edges.keys()
        }
        fn get_node_data<'a: 'n, 'n>(&'a self, node: &'n Self::Node) -> Option<&'a Self::NodeData> {
            self.nodes.get(node).map(|graph_data| graph_data.data())
        }
        fn get_edge_data<'a: 'n, 'n>(
            &'a self,
            edge: Self::EdgeRef<'n>,
        ) -> Option<&'a Self::EdgeData> {
            self.edges.get(edge)
        }
        fn successors<'a: 'n, 'n>(
            &'a self,
            node: &'n Self::Node,
        ) -> impl Iterator<Item = &'a Self::Node> {
            self.nodes
                .get(node)
                .into_iter()
                .flat_map(|graph_data| graph_data.successors())
        }
        fn predecessors<'a: 'n, 'n>(
            &'a self,
            node: &'n Self::Node,
        ) -> impl Iterator<Item = &'a Self::Node> {
            self.nodes
                .get(node)
                .into_iter()
                .flat_map(|graph_data| graph_data.predecessors())
        }
    };
}

macro_rules! impl_graph_mut {
    ($node:ty, $edge_entry:ty, $edge_entry_occupied:path, $edge_entry_vacant:path) => {
        type Edge = ($node, $node);
        type EdgeEntry<'n>
            = $edge_entry
        where
            Self: 'n;

        fn insert_node(&mut self, node: Self::Node, data: Self::NodeData) -> &mut Self::NodeData {
            match self.nodes.entry(node) {
                $edge_entry_occupied(entry) => {
                    let current = entry.into_mut().data_mut();
                    *current = data;
                    current
                }
                $edge_entry_vacant(entry) => entry.insert(GraphData::new(data)).data_mut(),
            }
        }
        fn get_or_insert_node(
            &mut self,
            node: Self::Node,
            f: impl FnOnce() -> Self::NodeData,
        ) -> &mut Self::NodeData {
            match self.nodes.entry(node) {
                $edge_entry_occupied(entry) => entry.into_mut().data_mut(),
                $edge_entry_vacant(entry) => entry.insert(GraphData::new(f())).data_mut(),
            }
        }
        fn get_mut_node_data(&mut self, node: &Self::Node) -> Option<&mut Self::NodeData> {
            Some(self.nodes.get_mut(node)?.data_mut())
        }
        fn remove_node(&mut self, node: &Self::Node) -> Option<Self::NodeData> {
            Some(self.nodes.remove(node)?.into_data())
        }
        fn get_edge_entry(&mut self, (from, to): Self::Edge) -> Option<Self::EdgeEntry<'_>> {
            if !self.nodes.contains_key(&from) || !self.nodes.contains_key(&to) {
                return None;
            }

            self.mut_graph_data(&from).add_successor(to.clone());
            self.mut_graph_data(&to).add_predecessor(from.clone());

            Some(self.edges.entry((from, to)))
        }
        fn get_mut_edge_data<'a: 'n, 'n>(
            &'a mut self,
            edge: Self::EdgeRef<'n>,
        ) -> Option<&'a mut Self::EdgeData> {
            self.edges.get_mut(edge)
        }
        fn remove_edge<'a: 'n, 'n>(
            &'a mut self,
            edge: Self::EdgeRef<'n>,
        ) -> Option<Self::EdgeData> {
            let previous_edge_data = self.edges.remove(edge)?;

            self.mut_graph_data(edge.from()).remove_successor(edge.to());
            self.mut_graph_data(edge.to())
                .remove_predecessor(edge.from());

            Some(previous_edge_data)
        }
    };
}

macro_rules! impl_graph_dot {
    () => {
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
    };
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BTreeGraph<
    N: Ord,
    ND,
    ED,
    GD: GraphData<Node = N, NodeData = ND> = BTreeGraphData<N, ND>,
> {
    nodes: BTreeMap<N, GD>,
    edges: BTreeMap<(N, N), ED>,
}

impl<N: Ord, ND, ED, GD: GraphData<Node = N, NodeData = ND>> BTreeGraph<N, ND, ED, GD> {
    impl_graph_methods!(N, GD);
}

impl<N: Ord, ND, ED, GD: GraphData<Node = N, NodeData = ND>> Default for BTreeGraph<N, ND, ED, GD> {
    impl_graph_default!();
}

impl<N: Ord, ND, ED, GD: GraphData<Node = N, NodeData = ND>> Graph for BTreeGraph<N, ND, ED, GD> {
    impl_graph!(N, ND, ED);
}

impl<N: Ord + Clone, ND, ED, GD: GraphData<Node = N, NodeData = ND>> GraphMut
    for BTreeGraph<N, ND, ED, GD>
{
    impl_graph_mut!(
        N,
        btree_map::Entry<'n, (N, N), ED>,
        btree_map::Entry::Occupied,
        btree_map::Entry::Vacant
    );
}

impl<N: Ord + Clone + Display, ND: Clone + Display, ED: Clone + Display> dot::Dot
    for BTreeGraph<N, ND, ED>
{
    impl_graph_dot!();
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashGraph<
    N: Hash + Eq,
    ND,
    ED,
    GD: GraphData<Node = N, NodeData = ND> = HashGraphData<N, ND>,
> {
    nodes: HashMap<N, GD>,
    edges: HashMap<(N, N), ED>,
}

impl<N: Hash + Eq, ND, ED, GD: GraphData<Node = N, NodeData = ND>> HashGraph<N, ND, ED, GD> {
    impl_graph_methods!(N, GD);
}

impl<N: Hash + Eq, ND, ED, GD: GraphData<Node = N, NodeData = ND>> Default
    for HashGraph<N, ND, ED, GD>
{
    impl_graph_default!();
}

impl<N: Hash + Eq, ND, ED, GD: GraphData<Node = N, NodeData = ND>> Graph
    for HashGraph<N, ND, ED, GD>
{
    impl_graph!(N, ND, ED);
}

impl<N: Hash + Eq + Clone, ND, ED, GD: GraphData<Node = N, NodeData = ND>> GraphMut
    for HashGraph<N, ND, ED, GD>
{
    impl_graph_mut!(
        N,
        hash_map::Entry<'n, (N, N), ED>,
        hash_map::Entry::Occupied,
        hash_map::Entry::Vacant
    );
}

impl<N: Hash + Eq + Display, ND: Display, ED: Display> dot::Dot for HashGraph<N, ND, ED> {
    impl_graph_dot!();
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OrdGraph<N: Ord, ND, ED, GD: GraphData<Node = N, NodeData = ND> = OrdGraphData<N, ND>> {
    nodes: OrdMap<N, GD>,
    edges: OrdMap<(N, N), ED>,
}

impl<N: Ord + Clone, ND: Clone, ED: Clone, GD: GraphData<Node = N, NodeData = ND> + Clone>
    OrdGraph<N, ND, ED, GD>
{
    impl_graph_methods!(N, GD);
}

impl<N: Ord + Clone, ND: Clone, ED: Clone, GD: GraphData<Node = N, NodeData = ND> + Clone> Default
    for OrdGraph<N, ND, ED, GD>
{
    impl_graph_default!();
}

impl<N: Ord, ND, ED, GD: GraphData<Node = N, NodeData = ND>> Graph for OrdGraph<N, ND, ED, GD> {
    impl_graph!(N, ND, ED);
}

impl<N: Ord + Clone, ND: Clone, ED: Clone, GD: GraphData<Node = N, NodeData = ND> + Clone> GraphMut
    for OrdGraph<N, ND, ED, GD>
{
    impl_graph_mut!(
        N,
        ordmap::Entry<'n, (N, N), ED, DefaultSharedPtr>,
        ordmap::Entry::Occupied,
        ordmap::Entry::Vacant
    );
}

impl<N: Ord + Clone + Display, ND: Clone + Display, ED: Clone + Display> dot::Dot
    for OrdGraph<N, ND, ED>
{
    impl_graph_dot!();
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImmutableHashGraph<
    N: Hash + Eq,
    ND,
    ED,
    GD: GraphData<Node = N, NodeData = ND> = ImmutableHashGraphData<N, ND>,
> {
    nodes: ImmutableHashMap<N, GD>,
    edges: ImmutableHashMap<(N, N), ED>,
}

impl<N: Hash + Eq + Clone, ND: Clone, ED: Clone, GD: GraphData<Node = N, NodeData = ND> + Clone>
    ImmutableHashGraph<N, ND, ED, GD>
{
    impl_graph_methods!(N, GD);
}

impl<N: Hash + Eq + Clone, ND: Clone, ED: Clone, GD: GraphData<Node = N, NodeData = ND> + Clone>
    Default for ImmutableHashGraph<N, ND, ED, GD>
{
    impl_graph_default!();
}

impl<N: Hash + Eq, ND, ED, GD: GraphData<Node = N, NodeData = ND>> Graph
    for ImmutableHashGraph<N, ND, ED, GD>
{
    impl_graph!(N, ND, ED);
}

impl<N: Hash + Eq + Clone, ND: Clone, ED: Clone, GD: GraphData<Node = N, NodeData = ND> + Clone>
    GraphMut for ImmutableHashGraph<N, ND, ED, GD>
{
    impl_graph_mut!(
        N,
        immutable_hashmap::Entry<'n, (N, N), ED, RandomState, DefaultSharedPtr>,
        immutable_hashmap::Entry::Occupied,
        immutable_hashmap::Entry::Vacant
    );
}

impl<N: Hash + Eq + Clone + Display, ND: Display, ED: Display> dot::Dot
    for ImmutableHashGraph<N, ND, ED>
{
    impl_graph_dot!();
}
