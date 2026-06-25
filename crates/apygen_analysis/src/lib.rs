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
    fn next_nodes(
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
        let abstract_environment =
            analyser.analyse_node(&mut abstract_environments, node.clone())?;

        for next_node in analyser.next_nodes(&node)? {
            let Some(updated_abstract_environment) = analyser.update_abstract_environment(
                &abstract_environments,
                &abstract_environment,
                node.clone(),
                next_node.clone(),
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
