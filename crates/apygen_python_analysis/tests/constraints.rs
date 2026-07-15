use apy::v1::{Identifier, QualifiedName};
use apygen_finder::filesystem::{AbsolutePathBuf, LocalFilesystem};
use apygen_finder::pathfinder::PathFinder;
use apygen_python_analysis::abstract_environment::BUILTINS_MODULE;
use apygen_python_analysis::constraints::{
    ModuleNode, QualifiedLocation, SpecCfgImporter, analyse_program,
};
use rstest::rstest;
use std::collections::{HashMap, HashSet};
use std::fs;
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

#[rstest]
fn test_builtins_constraint_generation() {
    init_logger();

    let absolute_manifest_dir = absolute_manifest_dir();
    let modules_dir = absolute_manifest_dir.join("tests/data/modules");

    let finder = PathFinder::new(
        Arc::new(LocalFilesystem),
        vec![modules_dir.clone()],
        Vec::new(),
        Some(modules_dir),
        Some(typeshed_dir()),
    );

    let specs: HashMap<Identifier, _> = finder.get_specs();

    let cfg_importer = SpecCfgImporter { specs };

    let builtins = Arc::new(QualifiedName::parse(BUILTINS_MODULE));

    let dependent_graph = analyse_program(&cfg_importer, HashSet::from_iter([builtins.clone()]));

    let actual_dot = dependent_graph.nodes[&ModuleNode::Module(builtins.clone())]
        [&QualifiedLocation::new(builtins.clone(), imbl::Vector::new())]
        .constraint_graph
        .dot("Constraints");

    let expected_dot_path = absolute_manifest_dir
        .join("tests/data/dot")
        .join(builtins.join())
        .with_extension("dot");

    if option_env!("GENERATE_DOT").is_some() {
        fs::write(&expected_dot_path, &actual_dot).expect("Failed to write DOT file");
    } else {
        let expected_dot =
            fs::read_to_string(&expected_dot_path).expect("DOT file should be readable");
        assert_eq!(expected_dot, actual_dot);
    }
}
