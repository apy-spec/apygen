pub use apygen_cfg as cfg;
use std::collections::BTreeSet;

pub mod lattice;
pub mod namespace;

pub trait GraphAnalyser {
    type Node;
    type AbstractEnvironment;
    type AbstractEnvironments;
    type Error;

    fn entry_node(&self) -> Result<Self::Node, Self::Error>;
    fn successors(
        &self,
        node: &Self::Node,
    ) -> Result<impl Iterator<Item = Self::Node>, Self::Error>;

    fn initialise_abstract_environments(&self) -> Result<Self::AbstractEnvironments, Self::Error>;
    fn analyse_node(
        &self,
        abstract_environments: &Self::AbstractEnvironments,
        node: Self::Node,
    ) -> Result<Self::AbstractEnvironment, Self::Error>;
    fn update_abstract_environment(
        &self,
        abstract_environments: &Self::AbstractEnvironments,
        abstract_environment: &Self::AbstractEnvironment,
        from: Self::Node,
        to: Self::Node,
    ) -> Result<Option<Self::AbstractEnvironment>, Self::Error>;
    fn get_abstract_environment(
        &self,
        abstract_environments: &Self::AbstractEnvironments,
        node: Self::Node,
    ) -> Result<Option<Self::AbstractEnvironment>, Self::Error>;
    fn set_abstract_environment(
        &self,
        abstract_environments: &mut Self::AbstractEnvironments,
        node: Self::Node,
        abstract_environment: &Self::AbstractEnvironment,
    ) -> Result<(), Self::Error>;

    fn merge(
        &self,
        abstract_environments: &Self::AbstractEnvironments,
        node: Self::Node,
        left: &Self::AbstractEnvironment,
        right: &Self::AbstractEnvironment,
    ) -> Result<Self::AbstractEnvironment, Self::Error>;
}

pub fn worklist<
    N: Clone + Ord,
    S: Eq,
    A,
    E,
    T: GraphAnalyser<Node = N, AbstractEnvironment = S, AbstractEnvironments = A, Error = E>,
>(
    analyser: &T,
) -> Result<A, E> {
    let mut abstract_environments = analyser.initialise_abstract_environments()?;

    let mut worklist = BTreeSet::from_iter([analyser.entry_node()?]);

    while let Some(node) = worklist.pop_first() {
        let res_abstract_environment =
            analyser.analyse_node(&mut abstract_environments, node.clone())?;

        for successor in analyser.successors(&node)? {
            let Some(res_cond_abstract_environment) = analyser.update_abstract_environment(
                &abstract_environments,
                &res_abstract_environment,
                node.clone(),
                successor.clone(),
            )?
            else {
                continue;
            };

            let (new_successor_is_equal, new_successor_abstract_environment) = match analyser
                .get_abstract_environment(&abstract_environments, successor.clone())?
            {
                Some(successor_abstract_environment) => {
                    let new_successor_abstract_environment = analyser.merge(
                        &abstract_environments,
                        successor.clone(),
                        &successor_abstract_environment,
                        &res_cond_abstract_environment,
                    )?;
                    (
                        new_successor_abstract_environment == successor_abstract_environment,
                        new_successor_abstract_environment,
                    )
                }
                None => (false, res_cond_abstract_environment),
            };

            if !new_successor_is_equal {
                analyser.set_abstract_environment(
                    &mut abstract_environments,
                    successor.clone(),
                    &new_successor_abstract_environment,
                )?;
                worklist.insert(successor);
            }
        }
    }

    Ok(abstract_environments)
}
