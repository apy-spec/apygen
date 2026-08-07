use std::collections::BTreeSet;

pub mod abstract_state;
pub mod fmt;
pub mod imbl;
pub mod lattice;
pub mod log;
pub mod rayon;

pub trait GraphAnalyser {
    type Node;
    type AbstractState;
    type AnalysisState;
    type Error;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error>;
    fn next_nodes(
        &self,
        node: &Self::Node,
    ) -> Result<impl Iterator<Item = &Self::Node>, Self::Error>;

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

    fn optimise(
        &self,
        _analysis_state: &mut Self::AnalysisState,
        _worklist: &mut BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
}

pub trait AnalysisObserver<N, S> {
    fn before_analysis(&mut self, _state: &S, _worklist: &BTreeSet<N>) {}
    fn before_iteration(&mut self, _state: &S, _worklist: &BTreeSet<N>) {}
    fn before_node_analysis(&mut self, _state: &S, _worklist: &BTreeSet<N>, _node: &N) {}
    fn after_node_analysis(&mut self, _state: &S, _worklist: &BTreeSet<N>, _node: &N) {}
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

        observer.before_node_analysis(&analysis_state, &worklist, &node);

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

        observer.after_node_analysis(&analysis_state, &worklist, &node);

        analyser.optimise(&mut analysis_state, &mut worklist)?;

        observer.after_iteration(&analysis_state, &worklist);
    }

    observer.after_analysis(&analysis_state, &worklist);

    Ok(analysis_state)
}

pub trait DependencyGraphAnalyser {
    type Node;
    type InputState;
    type OutputState;
    type AbstractState;
    type AnalysisState;
    type Error;

    fn entry_nodes(&self) -> Result<impl Iterator<Item = Self::Node>, Self::Error>;
    fn dependency_nodes<'a>(
        &'a self,
        analysis_state: &'a Self::AnalysisState,
        node: &'a Self::Node,
    ) -> Result<impl Iterator<Item = &'a Self::Node>, Self::Error>;
    fn dependent_nodes<'a>(
        &'a self,
        analysis_state: &'a Self::AnalysisState,
        node: &'a Self::Node,
    ) -> Result<impl Iterator<Item = &'a Self::Node>, Self::Error>;

    fn initialise_analysis_state(&self) -> Result<Self::AnalysisState, Self::Error>;
    fn analyse_node(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::AbstractState, Self::Error>;
    fn merge(
        &self,
        analysis_state: &Self::AnalysisState,
        abstract_state: Self::AbstractState,
    ) -> Result<Self::AnalysisState, Self::Error>;
    fn get_input_state(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::InputState, Self::Error>;
    fn get_output_state(
        &self,
        analysis_state: &Self::AnalysisState,
        node: &Self::Node,
    ) -> Result<Self::OutputState, Self::Error>;
    fn optimise(
        &self,
        _analysis_state: &mut Self::AnalysisState,
        _worklist: &mut BTreeSet<Self::Node>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
}

pub fn dependencies_analysis<
    N: Clone + Ord,
    I: Eq,
    R: Eq,
    A,
    E,
    T: DependencyGraphAnalyser<
            Node = N,
            InputState = I,
            OutputState = R,
            AnalysisState = A,
            Error = E,
        >,
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

        observer.before_node_analysis(&analysis_state, &worklist, &node);

        let abstract_state = analyser.analyse_node(&analysis_state, &node)?;

        let new_analysis_state = analyser.merge(&analysis_state, abstract_state)?;

        for dependency in analyser.dependency_nodes(&new_analysis_state, &node)? {
            if analyser.get_input_state(&analysis_state, dependency)?
                != analyser.get_input_state(&new_analysis_state, dependency)?
            {
                worklist.insert(dependency.clone());
            }
        }

        if analyser.get_output_state(&analysis_state, &node)?
            != analyser.get_output_state(&new_analysis_state, &node)?
        {
            for dependent in analyser.dependent_nodes(&new_analysis_state, &node)? {
                worklist.insert(dependent.clone());
            }
        }

        analysis_state = new_analysis_state;

        observer.after_node_analysis(&analysis_state, &worklist, &node);

        analyser.optimise(&mut analysis_state, &mut worklist)?;

        observer.after_iteration(&analysis_state, &worklist);
    }

    observer.after_analysis(&analysis_state, &worklist);

    Ok(analysis_state)
}
