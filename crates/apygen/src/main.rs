use apy;
use apygen_python_analysis::abstract_environment::Identifier;
use apygen_python_analysis::converter::v1::convert_apy_v1;
use apygen_python_analysis::finder::filesystem::{AbsolutePathBuf, LocalFilesystem};
use apygen_python_analysis::finder::pathfinder::PathFinder;
use apygen_python_analysis::worklist::cfg_worklist;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::path::PathBuf;
use std::sync::Arc;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let python_paths = vec![];
    let working_dir = AbsolutePathBuf::try_from(PathBuf::from("."))?;

    let finder = PathFinder::new(
        Arc::new(LocalFilesystem),
        python_paths,
        Vec::new(),
        Some(working_dir),
        None,
    );

    let specs: HashMap<Identifier, _> = finder.get_specs();

    let target_modules: HashSet<_> = specs
        .par_iter()
        .filter_map(|(identifier, finder_spec)| {
            if finder
                .working_directory()
                .is_some_and(|working_directory| finder_spec.spec.is_inside(working_directory))
            {
                Some(identifier.clone())
            } else {
                None
            }
        })
        .collect();

    let (namespaces, cfgs) = cfg_worklist(specs, target_modules).unwrap();

    let apy_v1_spec = convert_apy_v1(&namespaces, &cfgs);

    let apy_spec = apy::Apy::V1(apy_v1_spec);

    apy_spec.to_json_writer(File::create("apy.json")?)?;
    apy_spec.to_yaml_writer(&mut File::create("apy.yaml")?)?;

    Ok(())
}
