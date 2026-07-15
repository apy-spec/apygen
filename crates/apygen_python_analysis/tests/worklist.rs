use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::log::LogAnalysisObserver;
use apygen_analysis::rayon::par_analysis;
use apygen_finder::filesystem::{AbsolutePathBuf, LocalFilesystem};
use apygen_finder::pathfinder::PathFinder;
use apygen_python_analysis::abstract_environment::BUILTINS_MODULE;
use apygen_python_analysis::constraints::{ModuleNode, SpecCfgImporter, analyse_program};
use apygen_python_analysis::converter::v1::convert_apy_v1;
use apygen_python_analysis::solver::ModuleConstraintSolver;
use rayon::iter::ParallelBridge;
use rayon::iter::ParallelIterator;
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

    let cfg_importer = SpecCfgImporter { specs };

    let dependent_graph = analyse_program(&cfg_importer, target_modules);

    let solver = ModuleConstraintSolver::new(&dependent_graph);

    let program_evaluation = par_analysis(&solver, &mut LogAnalysisObserver::default())
        .expect("analysis should work")
        .abstract_states[&ModuleNode::Exit]
        .clone();

    let apy_v1 = convert_apy_v1(
        &program_evaluation,
        dependent_graph
            .nodes
            .keys()
            .par_bridge()
            .filter_map(|module_node| {
                if let ModuleNode::Module(module_name) = module_node {
                    if module_name.as_ref() != BUILTINS_MODULE {
                        Some(module_name)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }),
    );

    apy::Apy::V1(apy_v1)
}

#[rstest]
#[case::simple_variable_inference("simple_variable_inference")]
#[case::simple_function_call("simple_function_call")]
#[case::simple_function_argument_inference("simple_function_argument_inference")]
#[case::simple_class_init("simple_class_init")]
#[case::simple_class_inheritance("simple_class_inheritance")]
#[case::int_conversion("int_conversion")]
#[case::literal_int("literal_int")]
#[case::literal_boolean("literal_boolean")]
#[case::literal_bytes("literal_bytes")]
#[case::literal_str("literal_str")]
#[case::literal_float("literal_float")]
#[case::literal_ellipsis("literal_ellipsis")]
#[case::literal_none("literal_none")]
#[case::int_literal_inference("int_literal_inference")]
#[case::big_int_literal_inference("big_int_literal_inference")]
#[case::list_operations("list_operations")]
#[case::overloaded_function("overloaded_function")]
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
    let mut actual_apy_path = File::create(&expected_apy_path).expect("APY file should exist");
    actual_apy
        .to_yaml_writer(&mut actual_apy_path)
        .expect("TODO: panic message");

    let expected_apy_file = File::open(&expected_apy_path).expect("APY file should exist");
    let expected_apy =
        apy::Apy::from_yaml_reader(expected_apy_file).expect("APY file should be valid");

    assert_eq!(actual_apy, expected_apy);
}
