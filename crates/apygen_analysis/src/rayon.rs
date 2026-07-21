use crate::{AnalysisObserver, GraphAnalyser};
use rayon::prelude::*;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

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
            .map(|analysed_nodes| {
                analysed_nodes?
                    .into_par_iter()
                    .map(|(node, next_node, abstract_state)| {
                        if let Some(updated_abstract_state) = analyser.update_abstract_state(
                            &analysis_state,
                            &node,
                            &next_node,
                            &abstract_state,
                        )? {
                            Ok(Some((next_node, updated_abstract_state)))
                        } else {
                            Ok(None)
                        }
                    })
                    .filter_map(|next_abstract_state| next_abstract_state.transpose())
                    .collect::<Result<Vec<_>, _>>()
            })
            .map(|updated_nodes| {
                updated_nodes?
                    .into_par_iter()
                    .map(|(next_node, updated_abstract_state)| {
                        match analyser.get_abstract_state(&analysis_state, &next_node)? {
                            Some(next_node_abstract_state) => {
                                let new_abstract_state = analyser.merge(
                                    &analysis_state,
                                    &next_node,
                                    &next_node_abstract_state,
                                    &updated_abstract_state,
                                )?;
                                if new_abstract_state != updated_abstract_state {
                                    Ok(Some((next_node, new_abstract_state)))
                                } else {
                                    Ok(None)
                                }
                            }
                            None => Ok(Some((next_node, updated_abstract_state))),
                        }
                    })
                    .filter_map(|new_abstract_state| new_abstract_state.transpose())
                    .collect::<Result<BTreeMap<_, _>, _>>()
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
                                let current = entry.into_mut();
                                *current = analyser.merge(
                                    &analysis_state,
                                    &next_node,
                                    current,
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
            analyser.set_abstract_state(&mut analysis_state, &next_node, new_abstract_state)?;
            worklist.insert(next_node.clone());
        }

        observer.after_iteration(&analysis_state, &worklist);
    }

    observer.after_analysis(&analysis_state, &worklist);

    Ok(analysis_state)
}
