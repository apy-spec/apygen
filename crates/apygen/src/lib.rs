pub use apy;
pub use apygen_analysis as analysis;
pub use apygen_constraint_builder as constraint_builder;
pub use apygen_constraint_solver as constraint_solver;
pub use apygen_converter as converter;
pub use apygen_finder as finder;

pub use crate::apy::Apy;
pub use crate::finder::filesystem::{AbsolutePathBuf, Filesystem};

use crate::analysis::log::LogAnalysisObserver;
use crate::analysis::rayon::par_analysis;
use crate::constraint_builder::constraint_graph::ModuleNode;
use crate::constraint_builder::constraint_graph::expressions::{Identifier, QualifiedName};
use crate::constraint_builder::{SpecModuleLoader, analyse_program};
use crate::constraint_solver::ModuleConstraintSolver;
use crate::converter::v1::convert_apy_v1;
use crate::finder::pathfinder::PathFinder;

use log::debug;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

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

    let module_loader = SpecModuleLoader { specs };

    let dependent_graph = analyse_program(&module_loader, target_modules.into_iter());

    let solver = ModuleConstraintSolver::new(&dependent_graph);

    let program_evaluation = par_analysis(&solver, &mut LogAnalysisObserver::default())
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
