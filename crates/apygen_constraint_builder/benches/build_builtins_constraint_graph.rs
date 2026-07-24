use apygen_constraint_builder::constraint_graph::identifiers::SmolStr;
use apygen_constraint_builder::finder::filesystem::{AbsolutePathBuf, LocalFilesystem};
use apygen_constraint_builder::finder::pathfinder::PathFinder;
use apygen_constraint_builder::{SpecModuleLoader, analyse_program};
use criterion::{Criterion, criterion_group, criterion_main};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

fn typeshed_dir() -> AbsolutePathBuf {
    AbsolutePathBuf::try_from(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../vendor/typeshed/stdlib")
            .canonicalize()
            .expect("vendor/typeshed/stdlib should exist"),
    )
    .expect("canonicalized path is always absolute")
}

fn build_builtins_constraints(module_loader: &SpecModuleLoader<LocalFilesystem>) {
    analyse_program(module_loader, std::iter::empty());
}

fn bench_constraint_builder(criterion: &mut Criterion) {
    let finder = PathFinder::new(
        Arc::new(LocalFilesystem),
        vec![],
        Vec::new(),
        None,
        Some(typeshed_dir()),
    );

    let specs: HashMap<SmolStr, _> = finder.get_specs();

    let module_loader = SpecModuleLoader { specs };

    criterion.bench_function("build builtins constraints", |bencher| {
        bencher.iter(|| build_builtins_constraints(&module_loader))
    });
}

criterion_group!(benches, bench_constraint_builder);
criterion_main!(benches);
