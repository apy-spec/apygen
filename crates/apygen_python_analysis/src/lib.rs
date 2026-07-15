use crate::constraints::{ModuleNode, SpecCfgImporter, analyse_program};
use crate::converter::v1::convert_apy_v1;
use crate::solver::ModuleConstraintSolver;
pub use apy;
use apy::v1::{Identifier, QualifiedName};
pub use apygen_analysis as analysis;
use apygen_analysis::analysis;
use apygen_analysis::log::LogAnalysisObserver;
pub use apygen_finder as finder;
pub use finder::filesystem::{AbsolutePathBuf, Filesystem, LocalFilesystem};
pub use finder::pathfinder::PathFinder;
use log::debug;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub mod abstract_environment;
pub mod constraints;
pub mod converter;
pub mod genkill;
pub mod solver;
pub mod worklist;

pub fn analyse_workdir(
    filesystem: impl Filesystem,
    python_paths: Vec<AbsolutePathBuf>,
    stubs_paths: Vec<AbsolutePathBuf>,
    working_directory: AbsolutePathBuf,
    typeshed_path: Option<AbsolutePathBuf>,
) -> apy::Apy {
    let finder = PathFinder::new(
        Arc::new(filesystem),
        python_paths,
        stubs_paths,
        Some(working_directory),
        typeshed_path,
    );

    let specs: HashMap<Identifier, _> = finder.get_specs();

    let target_modules: HashSet<_> = specs
        .par_iter()
        .filter_map(|(identifier, finder_spec)| {
            if finder_spec.spec.is_inside(finder.working_directory()?) {
                Some(Arc::new(QualifiedName::from(identifier.clone())))
            } else {
                None
            }
        })
        .collect();

    let cfg_importer = SpecCfgImporter { specs };

    let dependent_graph = analyse_program(&cfg_importer, target_modules);

    let solver = ModuleConstraintSolver::new(&dependent_graph);

    let program_evaluation = analysis(&solver, &mut LogAnalysisObserver::default())
        .expect("analysis should work")
        .abstract_states[&ModuleNode::Exit]
        .clone();

    debug!("Modules: {}", dependent_graph.nodes.len());

    let apy_v1 = convert_apy_v1(
        &program_evaluation,
        dependent_graph
            .nodes
            .keys()
            .par_bridge()
            .filter_map(|module_node| {
                if let ModuleNode::Module(module_name) = module_node {
                    Some(module_name)
                } else {
                    None
                }
            }),
    );

    apy::Apy::V1(apy_v1)
}
