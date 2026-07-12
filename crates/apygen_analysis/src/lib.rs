pub use apygen_cfg as cfg;
use std::collections::BTreeSet;

pub mod imbl;
pub mod lattice;
pub mod log;
pub mod namespace;
pub mod rayon;
pub mod fmt;
pub mod abstract_state;

pub trait GraphAnalyser {
    type Node;
    type AbstractState;
    type AnalysisState;
    type Error;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error>;
    fn next_nodes<'a>(
        &'a self,
        node: &'a Self::Node,
    ) -> Result<impl Iterator<Item = &'a Self::Node>, Self::Error>;

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error>;
    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::AbstractState, Self::Error>;
    fn update_abstract_state(
        &self,
        analysis_state: &Self::AnalysisState,
        from: &Self::Node,
        to: &Self::Node,
        abstract_state: &Self::AbstractState,
    ) -> Result<Option<Self::AbstractState>, Self::Error>;
    fn get_abstract_state<'a>(
        &self,
        analysis_state: &'a Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Option<&'a Self::AbstractState>, Self::Error>;
    fn set_abstract_state(
        &self,
        analysis_state: &mut Self::AnalysisState,
        node: &Self::Node,
        abstract_state: Self::AbstractState,
    ) -> Result<(), Self::Error>;

    fn merge(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
        left: &Self::AbstractState,
        right: &Self::AbstractState,
    ) -> Result<Self::AbstractState, Self::Error>;
}

pub trait AnalysisObserver<N, S> {
    fn before_analysis(&mut self, _state: &S, _worklist: &BTreeSet<N>) {}
    fn before_iteration(&mut self, _state: &S, _worklist: &BTreeSet<N>) {}
    fn after_iteration(&mut self, _state: &S, _worklist: &BTreeSet<N>) {}
    fn after_analysis(&mut self, _state: &S, _worklist: &BTreeSet<N>) {}
}

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DummyAnalysisObserver;

impl<N, S> AnalysisObserver<N, S> for DummyAnalysisObserver {}

pub fn analysis<
    N: Clone + Ord,
    S: Eq,
    A,
    E,
    T: GraphAnalyser<Node = N, AbstractState = S, AnalysisState = A, Error = E>,
    O: AnalysisObserver<N, A>,
>(
    analyser: &T,
    observer: &mut O,
) -> Result<A, E> {
    let mut analysis_state = analyser.initialise_analysis_state()?;

    let mut worklist = BTreeSet::from_iter(analyser.entry_nodes()?);

    observer.before_analysis(&analysis_state, &worklist);

    loop {
        observer.before_iteration(&analysis_state, &worklist);

        let Some(node) = worklist.pop_first() else {
            break;
        };

        let abstract_state = analyser.analyse_node(&analysis_state, &node)?;

        for next_node in analyser.next_nodes(&node)? {
            let Some(updated_abstract_state) = analyser.update_abstract_state(
                &analysis_state,
                &node,
                next_node,
                &abstract_state,
            )?
            else {
                continue;
            };

            let (should_update, new_abstract_state) =
                match analyser.get_abstract_state(&analysis_state, next_node)? {
                    Some(next_node_abstract_state) => {
                        let new_abstract_state = analyser.merge(
                            &analysis_state,
                            next_node,
                            &next_node_abstract_state,
                            &updated_abstract_state,
                        )?;
                        (
                            new_abstract_state != *next_node_abstract_state,
                            new_abstract_state,
                        )
                    }
                    None => (true, updated_abstract_state),
                };

            if should_update {
                analyser.set_abstract_state(&mut analysis_state, &next_node, new_abstract_state)?;
                worklist.insert(next_node.clone());
            }
        }

        observer.after_iteration(&analysis_state, &worklist);
    }

    observer.after_analysis(&analysis_state, &worklist);

    Ok(analysis_state)
}
