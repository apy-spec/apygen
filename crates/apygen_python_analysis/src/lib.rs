use crate::converter::v1::convert_apy_v1;
use crate::worklist::cfg_worklist;
pub use apy;
use apy::v1::Identifier;
pub use apygen_analysis as analysis;
pub use apygen_finder as finder;
pub use finder::filesystem::{AbsolutePathBuf, Filesystem, LocalFilesystem};
pub use finder::pathfinder::PathFinder;
use log::debug;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub mod abstract_environment;
pub mod converter;
pub mod genkill;
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
                Some(identifier.clone())
            } else {
                None
            }
        })
        .collect();

    let (namespaces, cfgs) = cfg_worklist(specs, &target_modules).unwrap();

    debug!("Modules: {}", cfgs.len());
    debug!("Locations: {}", namespaces.locations.len());

    let apy_v1 = convert_apy_v1(&namespaces, cfgs.keys().par_bridge());

    apy::Apy::V1(apy_v1)
}
