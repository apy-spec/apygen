pub mod dot;

pub trait Graph {
    type Node: Eq;
    type NodeData;
    type EdgeData;
    fn node_data_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::NodeData)>;
    fn edge_data_iter(&self)
    -> impl Iterator<Item = ((&Self::Node, &Self::Node), &Self::EdgeData)>;
    fn node_iter(&self) -> impl Iterator<Item = &Self::Node> {
        self.node_data_iter().map(|(node, _)| node)
    }
    fn edge_iter(&self) -> impl Iterator<Item = (&Self::Node, &Self::Node)> {
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
    fn get_edge_data(&self, edge: (&Self::Node, &Self::Node)) -> Option<&Self::EdgeData> {
        for (e, edge_data) in self.edge_data_iter() {
            if e == edge {
                return Some(edge_data);
            }
        }
        None
    }
    fn successor_iter(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
        self.edge_iter()
            .filter_map(move |(from, to)| if from == node { Some(to) } else { None })
    }
    fn predecessor_iter(&self, node: &Self::Node) -> impl Iterator<Item = &Self::Node> {
        self.edge_iter()
            .filter_map(move |(from, to)| if to == node { Some(from) } else { None })
    }
}
