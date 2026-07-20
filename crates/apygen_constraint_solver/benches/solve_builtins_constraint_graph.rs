use apygen_constraint_builder::finder::filesystem::{AbsolutePathBuf, LocalFilesystem};
use apygen_constraint_builder::finder::pathfinder::PathFinder;
use apygen_constraint_builder::{SpecModuleLoader, analyse_program};

use apygen_constraint_solver::ModuleConstraintSolver;
use apygen_constraint_solver::analysis::DummyAnalysisObserver;
use apygen_constraint_solver::analysis::rayon::par_analysis;
use apygen_constraint_solver::constraint_graph::ModuleDependentGraph;
use apygen_constraint_solver::constraint_graph::expressions::Identifier;

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

fn solve_builtins_constraints(module_dependent_graph: &ModuleDependentGraph) {
    let solver = ModuleConstraintSolver::new(module_dependent_graph);

    par_analysis(&solver, &mut DummyAnalysisObserver::default()).expect("analysis should work");
}

fn bench_constraint_solver(criterion: &mut Criterion) {
    let finder = PathFinder::new(
        Arc::new(LocalFilesystem),
        vec![],
        Vec::new(),
        None,
        Some(typeshed_dir()),
    );

    let specs: HashMap<Identifier, _> = finder.get_specs();

    let module_loader = SpecModuleLoader { specs };

    let module_dependent_graph = analyse_program(&module_loader, std::iter::empty());

    criterion.bench_function("solve builtins constraints", |bencher| {
        bencher.iter(|| solve_builtins_constraints(&module_dependent_graph))
    });
}

criterion_group!(benches, bench_constraint_solver);
criterion_main!(benches);
