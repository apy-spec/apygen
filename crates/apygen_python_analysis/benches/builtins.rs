use apy::v1::{Identifier, QualifiedName};
use apygen_finder::filesystem::{AbsolutePathBuf, LocalFilesystem};
use apygen_finder::pathfinder::PathFinder;
use apygen_python_analysis::abstract_environment::BUILTINS_MODULE;
use apygen_python_analysis::constraints::{SpecCfgImporter, analyse_program};
use criterion::{Criterion, criterion_group, criterion_main};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

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

fn build_constraints() {
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

    analyse_program(&cfg_importer, HashSet::from_iter([builtins.clone()]));
}

fn bench_constraint_builder(criterion: &mut Criterion) {
    criterion.bench_function("builtins constraints", |bencher| {
        bencher.iter(|| build_constraints())
    });
}

criterion_group!(benches, bench_constraint_builder);
criterion_main!(benches);
