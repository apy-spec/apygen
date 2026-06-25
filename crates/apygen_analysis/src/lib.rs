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
    fn update_abstract_environment(
        &self,
        analysis_state: &Self::AnalysisState,
        from: Self::Node,
        to: Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error>;
    fn get_abstract_environment(
        &self,
        analysis_state: &Self::AnalysisState,
        node: Self::Node,
    ) -> Result<Option<Self::AbstractState>, Self::Error>;
    fn set_abstract_environment(
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

pub fn worklist<
    N: Clone + Ord,
    S: Eq,
    A,
    E,
    T: GraphAnalyser<Node = N, AbstractState = S, AnalysisState = A, Error = E>,
>(
    analyser: &T,
) -> Result<A, E> {
    let mut abstract_environments = analyser.initialise_analysis_state()?;

    let mut worklist = BTreeSet::from_iter([analyser.entry_node()?]);

    while let Some(node) = worklist.pop_first() {
        let abstract_environment =
            analyser.analyse_node(&mut abstract_environments, node.clone())?;

        for next_node in analyser.next_nodes(&node)? {
            let Some(updated_abstract_environment) = analyser.update_abstract_environment(
                &abstract_environments,
                node.clone(),
                next_node.clone(),
                &abstract_environment,
            )?
            else {
                continue;
            };

            let (should_update, new_abstract_environment) = match analyser
                .get_abstract_environment(&abstract_environments, next_node.clone())?
            {
                Some(next_node_abstract_environment) => {
                    let new_abstract_environment = analyser.merge(
                        &abstract_environments,
                        next_node.clone(),
                        &next_node_abstract_environment,
                        &updated_abstract_environment,
                    )?;
                    (
                        new_abstract_environment != next_node_abstract_environment,
                        new_abstract_environment,
                    )
                }
                None => (true, updated_abstract_environment),
            };

            if should_update {
                analyser.set_abstract_environment(
                    &mut abstract_environments,
                    next_node.clone(),
                    &new_abstract_environment,
                )?;
                worklist.insert(next_node);
            }
        }
    }

    Ok(abstract_environments)
}
