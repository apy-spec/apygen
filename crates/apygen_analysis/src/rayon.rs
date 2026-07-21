use crate::{AnalysisObserver, GraphAnalyser};
use rayon::prelude::*;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

fn update_merge<N: Clone + Ord, S, A, E>(
    analyser: &impl GraphAnalyser<Node = N, AbstractState = S, AnalysisState = A, Error = E>,
    analysis_state: &A,
    abstract_states: &mut BTreeMap<N, S>,
    node: N,
    state: S,
) -> Result<(), E> {
    match abstract_states.entry(node.clone()) {
        Entry::Vacant(entry) => {
            entry.insert(state);
        }
        Entry::Occupied(entry) => {
            let current = entry.into_mut();
            *current = analyser.merge(&analysis_state, &node, current, &state)?
        }
    }
    Ok(())
}

pub fn par_analysis<
    N: Clone + Ord + Send,
    S: Eq + Clone + Send,
    A: Sync,
    E: Send,
    T: Send + Sync + GraphAnalyser<Node = N, AbstractState = S, AnalysisState = A, Error = E>,
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

        if worklist.is_empty() {
            break;
        }

        let new_states = worklist
            .into_par_iter()
            .map(|node| {
                let abstract_state = analyser.analyse_node(&analysis_state, &node)?;

                Ok(analyser
                    .next_nodes(&node)?
                    .map(|next_node| (node.clone(), next_node.clone(), abstract_state.clone()))
                    .collect::<Vec<_>>())
            })
            .try_reduce(
                || Vec::new(),
                |mut acc, analysed_nodes| {
                    acc.extend(analysed_nodes);
                    Ok(acc)
                },
            )?
            .into_par_iter()
            .map(|(node, next_node, abstract_state)| {
                let Some(updated_abstract_state) = analyser.update_abstract_state(
                    &analysis_state,
                    &node,
                    &next_node,
                    &abstract_state,
                )?
                else {
                    return Ok(None);
                };

                Ok(
                    match analyser.get_abstract_state(&analysis_state, &next_node)? {
                        Some(next_node_abstract_state) => {
                            let new_abstract_state = analyser.merge(
                                &analysis_state,
                                &next_node,
                                &next_node_abstract_state,
                                &updated_abstract_state,
                            )?;
                            if new_abstract_state != updated_abstract_state {
                                Some((next_node, new_abstract_state))
                            } else {
                                None
                            }
                        }
                        None => Some((next_node, updated_abstract_state)),
                    },
                )
            })
            .try_fold(
                || BTreeMap::new(),
                |mut acc, new_abstract_state_option| {
                    if let Some((next_node, new_state)) = new_abstract_state_option? {
                        update_merge(analyser, &analysis_state, &mut acc, next_node, new_state)?;
                    }
                    Ok(acc)
                },
            )
            .try_reduce(
                || BTreeMap::new(),
                |mut acc, new_states| {
                    for (next_node, new_state) in new_states {
                        update_merge(analyser, &analysis_state, &mut acc, next_node, new_state)?;
                    }
                    Ok(acc)
                },
            )?;

        worklist = BTreeSet::new();
        for (next_node, new_abstract_state) in new_states {
            analyser.set_abstract_state(&mut analysis_state, &next_node, new_abstract_state)?;
            worklist.insert(next_node.clone());
        }

        observer.after_iteration(&analysis_state, &worklist);
    }

    observer.after_analysis(&analysis_state, &worklist);

    Ok(analysis_state)
}
