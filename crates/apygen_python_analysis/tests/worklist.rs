use apy::v1::{Identifier, QualifiedName};
use apygen_finder::filesystem::{AbsolutePathBuf, LocalFilesystem};
use apygen_finder::pathfinder::PathFinder;
use apygen_python_analysis::converter::v1::convert_apy_v1;
use apygen_python_analysis::worklist::cfg_worklist;
use rstest::rstest;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::fs::File;
use std::path::PathBuf;
use std::sync::Arc;

fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}

fn absolute_manifest_dir() -> AbsolutePathBuf {
    AbsolutePathBuf::try_from(PathBuf::from(env!("CARGO_MANIFEST_DIR")))
        .expect("MANIFEST_DIR should be an absolute path")
}

fn typeshed_dir() -> AbsolutePathBuf {
    AbsolutePathBuf::try_from(
        fs::canonicalize(
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/typeshed/stdlib"),
        )
        .expect("vendor/typeshed/stdlib should exist"),
    )
    .expect("canonicalized path is always absolute")
}

pub fn analyse_directory(
    directory: AbsolutePathBuf,
    target_modules: HashSet<Arc<QualifiedName>>,
) -> apy::Apy {
    let finder = PathFinder::new(
        Arc::new(LocalFilesystem),
        vec![directory.clone()],
        Vec::new(),
        Some(directory),
        Some(typeshed_dir()),
    );

    let specs: HashMap<Identifier, _> = finder.get_specs();

    let (namespaces, _) = cfg_worklist(
        specs,
        &target_modules
            .iter()
            .map(|name| name.identifiers.first().clone())
            .collect::<HashSet<_>>(),
    )
    .expect("cfg_worklist should succeed");

    let apy_v1 = convert_apy_v1(&namespaces, &target_modules);

    apy::Apy::V1(apy_v1)
}

#[rstest]
#[case::simple_variable_inference("simple_variable_inference")]
fn test_inference(#[case] module_name: String) {
    init_logger();

    let absolute_manifest_dir = absolute_manifest_dir();
    let modules_dir = absolute_manifest_dir.join("tests/data/modules");

    let actual_apy = analyse_directory(
        modules_dir,
        HashSet::from_iter([Arc::new(QualifiedName::parse(&module_name))]),
    );

    let expected_apy_path = absolute_manifest_dir
        .join("tests/data/apy")
        .join(&module_name)
        .with_extension("yaml");
    let expected_apy_file = File::open(&expected_apy_path).expect("APY file should exist");
    let expected_apy =
        apy::Apy::from_yaml_reader(expected_apy_file).expect("APY file should be valid");

    assert_eq!(actual_apy, expected_apy);
}
