use crate::GraphAnalyser;
use rayon::prelude::*;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

pub fn par_analysis<
    N: Clone + Ord + Send,
    S: Eq + Send,
    A: Sync,
    E: Send,
    T: Send + Sync + GraphAnalyser<Node = N, AbstractState = S, AnalysisState = A, Error = E>,
>(
    analyser: &T,
) -> Result<A, E> {
    let mut analysis_state = analyser.initialise_analysis_state()?;

    let mut analysis_metadata = analyser.initialise_analysis_metadata()?;

    let mut worklist = BTreeSet::from_iter(analyser.entry_nodes()?);

    analyser.before_analysis(&mut analysis_metadata, &analysis_state, &worklist)?;

    loop {
        analyser.before_iteration(&mut analysis_metadata, &analysis_state, &worklist)?;

        if worklist.is_empty() {
            break;
        }

        let new_states = worklist
            .into_par_iter()
            .map(|node| {
                let mut new_abstract_states = BTreeMap::new();

                let abstract_state = analyser.analyse_node(&analysis_state, node.clone())?;

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
                        match analyser.get_abstract_state(&analysis_state, &next_node)? {
                            Some(next_node_abstract_state) => {
                                let new_abstract_state = analyser.merge(
                                    &analysis_state,
                                    next_node.clone(),
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
                        new_abstract_states.insert(next_node.clone(), new_abstract_state);
                    }
                }

                Ok(new_abstract_states)
            })
            .try_reduce(
                || BTreeMap::new(),
                |mut acc, new_states| {
                    for (next_node, new_state) in new_states {
                        match acc.entry(next_node.clone()) {
                            Entry::Vacant(entry) => {
                                entry.insert(new_state);
                            }
                            Entry::Occupied(entry) => {
                                let entry = entry.into_mut();
                                *entry = analyser.merge(
                                    &analysis_state,
                                    next_node.clone(),
                                    entry,
                                    &new_state,
                                )?
                            }
                        }
                    }
                    Ok(acc)
                },
            )?;

        worklist = BTreeSet::new();
        for (next_node, new_abstract_state) in new_states {
            analyser.set_abstract_state(
                &mut analysis_state,
                next_node.clone(),
                new_abstract_state,
            )?;
            worklist.insert(next_node.clone());
        }

        analyser.after_iteration(&mut analysis_metadata, &analysis_state, &worklist)?;
    }

    analyser.after_analysis(&mut analysis_metadata, &analysis_state, &worklist)?;

    Ok(analysis_state)
}
