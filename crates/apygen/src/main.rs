use apy;
use apygen_python_analysis::converter::v1::convert_apy_v1;
use apygen_python_analysis::finder::filesystem::{AbsolutePathBuf, LocalFilesystem};
use apygen_python_analysis::finder::pathfinder::PathFinder;
use apygen_python_analysis::worklist::cfg_worklist;
use rayon::prelude::*;
use std::collections::HashSet;
use std::fs::File;
use std::path::PathBuf;
use std::sync::Arc;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let python_paths = vec![];
    let working_dir = AbsolutePathBuf::try_from(PathBuf::from("."))?;

    let finder = PathFinder::new(Arc::new(LocalFilesystem), python_paths);

    let module_specs = finder.get_all_specs();

    let initial_worklist: HashSet<_> = module_specs
        .par_iter()
        .filter_map(|(qualified_name, module_spec)| {
            if module_spec.is_inside(&working_dir) {
                Some(qualified_name.clone())
            } else {
                None
            }
        })
        .collect();

    let (namespaces, cfgs) = cfg_worklist(module_specs, initial_worklist).unwrap();

    let apy_v1_spec = convert_apy_v1(&namespaces, &cfgs);

    let apy_spec = apy::Apy::V1(apy_v1_spec);

    apy_spec.to_json_writer(File::create("apy.json")?)?;
    apy_spec.to_yaml_writer(&mut File::create("apy.yaml")?)?;

    Ok(())
}
