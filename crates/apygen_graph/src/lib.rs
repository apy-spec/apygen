pub mod dot;

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
    type NodeData;
    type Edge: Edge<Node = Self::Node> + Eq;
    type EdgeData;
    fn node_data_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)>;
    fn edge_data_iter(&self) -> impl Iterator<Item = (&Self::Edge, &Self::EdgeData)>;
    fn node_iter(&self) -> impl Iterator<Item = &Self::Node> {
        self.node_data_iter().map(|(node, _)| node)
    }
    fn edge_iter(&self) -> impl Iterator<Item = &Self::Edge> {
        self.edge_data_iter().map(|(edge, _)| edge)
    }
    fn get_node_data(&self, node: &Self::Node) -> Option<&Self::NodeData> {
        for (n, node_data) in self.node_data_iter() {
            if n == node {
                return Some(node_data);
            }
        }
        None
    }
    fn get_edge_data(&self, edge: &Self::Edge) -> Option<&Self::EdgeData> {
        for (e, edge_data) in self.edge_data_iter() {
            if e == edge {
                return Some(edge_data);
            }
        }
        None
    }
    fn successor_iter(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
        self.edge_iter().filter_map(move |edge| {
            if edge.from() == node {
                Some(edge.to())
            } else {
                None
            }
        })
    }
    fn predecessor_iter(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
        self.edge_iter().filter_map(move |edge| {
            if edge.to() == node {
                Some(edge.from())
            } else {
                None
            }
        })
    }
}
