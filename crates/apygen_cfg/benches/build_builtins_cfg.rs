use apygen_cfg::build_cfg;
use apygen_cfg::parser::parse_module;
use apygen_cfg::source_file::LineIndex;
use criterion::{Criterion, criterion_group, criterion_main};
use std::fs;
use std::path::PathBuf;

fn absolute_manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn typeshed_dir() -> PathBuf {
    absolute_manifest_dir().join("../../vendor/typeshed/stdlib")
}

fn build_builtins_cfg() {
    let builtins_path = typeshed_dir().join("builtins.pyi");

    let builtins_source = fs::read_to_string(builtins_path).expect("builtins module should exists");

    let line_index = LineIndex::from_source_text(&builtins_source);
    let builtins_module = parse_module(&builtins_source).expect("builtins should be parsed");

    build_cfg(&line_index, builtins_module.syntax()).expect("builtins cfg should be built");
}

fn bench_cfg_builder(criterion: &mut Criterion) {
    criterion.bench_function("builtins cfg builder", |bencher| {
        bencher.iter(|| build_builtins_cfg())
    });
}

criterion_group!(benches, bench_cfg_builder);
criterion_main!(benches);
