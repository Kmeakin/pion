#![allow(
    clippy::as_conversions,
    clippy::collection_is_never_read,
    clippy::unit_arg,
    reason = "It's just a test"
)]

use std::path::{Path, PathBuf};

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use pion_surface::lex::lex;
use walkdir::{DirEntry, WalkDir};

const WORKSPACE_DIR: &str = env!("CARGO_WORKSPACE_DIR");
const TESTS_DIR: &str = "test-data";

fn bench_lex(c: &mut Criterion) {
    let all_test_files = all_test_files();
    let mut group = c.benchmark_group("lex");

    for repeat in [1, 10, 100] {
        let input = all_test_files.repeat(repeat);
        group.throughput(Throughput::Bytes(input.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(input.len()),
            &input,
            |b, input| {
                b.iter(|| {
                    for token in lex(input) {
                        black_box(token);
                    }
                });
            },
        );
    }
}

fn bench_lines(c: &mut Criterion) {
    let all_test_files = all_test_files();
    let mut group = c.benchmark_group("lines");

    for repeat in [1, 10, 100] {
        let input = all_test_files.repeat(repeat);
        group.throughput(Throughput::Bytes(input.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(input.len()),
            &input,
            |b, input| {
                b.iter(|| {
                    for line in input.lines() {
                        black_box(line.len());
                    }
                });
            },
        );
    }
}

fn bench_memcpy(c: &mut Criterion) {
    let all_test_files = all_test_files();
    let mut group = c.benchmark_group("memcpy");

    for repeat in [1, 10, 100, 1000] {
        let input = all_test_files.repeat(repeat);
        group.throughput(Throughput::Bytes(input.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(input.len()),
            &input,
            |b, input| {
                let mut buf = String::with_capacity(input.len());
                b.iter(|| {
                    buf.clear();
                    black_box(buf.push_str(input));
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

criterion_group!(benches, bench_memcpy, bench_lines, bench_lex);
criterion_main!(benches);
