pub use apygen_cfg as cfg;
use std::collections::BTreeSet;

pub mod lattice;
pub mod namespace;

pub trait GraphAnalyser {
    type Node;
    type AbstractState;
    type AnalysisState;
    type Error;

    fn entry_node(&self) -> Result<Self::Node, Self::Error>;
    fn next_nodes(
        &self,
        node: &Self::Node,
    ) -> Result<impl Iterator<Item = Self::Node>, Self::Error>;

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error>;
    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
    ) -> Result<Self::AbstractState, Self::Error>;
    fn update_abstract_state(
        &self,
        analysis_state: &Self::AnalysisState,
        from: Self::Node,
        to: Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error>;
    fn get_abstract_state(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
    ) -> Result<Option<Self::AbstractState>, Self::Error>;
    fn set_abstract_state(
        &self,
        analysis_state: &mut Self::AnalysisState,
        node: Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<(), Self::Error>;

    fn merge(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
        left: &Self::AbstractState,
        right: &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error>;
}

pub fn analysis<
    N: Clone + Ord,
    S: Eq,
    A,
    E,
    T: GraphAnalyser<Node = N, AbstractState = S, AnalysisState = A, Error = E>,
>(
    analyser: &T,
) -> Result<A, E> {
    let mut analysis_state = analyser.initialise_analysis_state()?;

    let mut worklist = BTreeSet::from_iter([analyser.entry_node()?]);

    while let Some(node) = worklist.pop_first() {
        let abstract_state = analyser.analyse_node(&mut analysis_state, node.clone())?;

        for next_node in analyser.next_nodes(&node)? {
            let Some(updated_abstract_state) = analyser.update_abstract_state(
                &analysis_state,
                node.clone(),
                next_node.clone(),
                &abstract_state,
            )?
            else {
                continue;
            };

            let (should_update, new_abstract_state) =
                match analyser.get_abstract_state(&analysis_state, next_node.clone())? {
                    Some(next_node_abstract_state) => {
                        let new_abstract_state = analyser.merge(
                            &analysis_state,
                            next_node.clone(),
                            &next_node_abstract_state,
                            &updated_abstract_state,
                        )?;
                        (
                            new_abstract_state != next_node_abstract_state,
                            new_abstract_state,
                        )
                    }
                    None => (true, updated_abstract_state),
                };

            if should_update {
                analyser.set_abstract_state(
                    &mut analysis_state,
                    next_node.clone(),
                    &new_abstract_state,
                )?;
                worklist.insert(next_node);
            }
        }
    }

    Ok(analysis_state)
}
