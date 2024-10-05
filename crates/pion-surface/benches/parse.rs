#![allow(
    clippy::as_conversions,
    clippy::collection_is_never_read,
    clippy::unit_arg,
    reason = "It's just a test"
)]

use std::path::{Path, PathBuf};

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use pion_surface::lex::lex;
use pion_surface::parse::parse_file;
use walkdir::{DirEntry, WalkDir};

const WORKSPACE_DIR: &str = env!("CARGO_WORKSPACE_DIR");
const TESTS_DIR: &str = "test-data";

fn bench_parse(c: &mut Criterion) {
    let all_test_files = all_test_files();
    let mut group = c.benchmark_group("parse");

    for repeat in [1, 10, 100] {
        let input = all_test_files.repeat(repeat);
        group.throughput(Throughput::Bytes(input.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(input.len()),
            &input,
            |b, input| {
                b.iter(|| {
                    let bump = bumpalo::Bump::new();
                    let tokens = lex(input);
                    let (file, diagnostics) = parse_file(0, tokens, &bump);
                    black_box((file, diagnostics));
                });
            },
        );
    }
}

/// Recursively walk over test files under a file path.
fn find_source_files(root: impl AsRef<Path>) -> impl Iterator<Item = PathBuf> {
    WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_file())
        .filter(|entry| matches!(entry.path().extension(), Some(ext) if ext == "pion"))
        .map(DirEntry::into_path)
}

fn all_test_files() -> String {
    let mut out = String::new();
    for path in find_source_files(format!("{WORKSPACE_DIR}/{TESTS_DIR}/elab")) {
        let text = std::fs::read_to_string(path).unwrap();
        out.push_str(&text);
        out.push('\n');
    }
    out
}

criterion_group!(benches, bench_parse);
criterion_main!(benches);
