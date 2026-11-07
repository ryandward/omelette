//! Latency of the golden cases, absence and mutation. Run with
//! `cargo run --release --example latency -- 500 --check`.
use omelette::{engine, lower};
use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_span::SourceType;
use std::hint::black_box;
use std::time::Instant;

/// Samples per case: parsing alone, parsing through lowering, and the whole evaluation.
#[derive(Clone, Default)]
struct Samples {
    parse: Vec<f64>,
    lower: Vec<f64>,
    total: Vec<f64>,
}

/// The sample at `percent`, rounding the rank up.
fn quantile(sorted: &[f64], percent: usize) -> f64 {
    sorted[((sorted.len() - 1) * percent).div_ceil(100)]
}

fn micros(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1e6
}

fn sample(src: &str, into: &mut Samples) {
    let start = Instant::now();
    {
        let arena = Allocator::default();
        black_box(Parser::new(&arena, black_box(src), SourceType::ts()).parse_expression().ok());
    }
    into.parse.push(micros(start));
    let start = Instant::now();
    black_box(lower::lower(black_box(src)).ok());
    into.lower.push(micros(start));
    let start = Instant::now();
    black_box(engine::evaluate(black_box(src)).ok());
    into.total.push(micros(start));
}

/// A golden case: which verdict it checks (the absence verdict, or the mutation verdict when
/// `mutation`), the expected one, and the source.
#[derive(Clone, Copy)]
struct Case<'s> {
    mutation: bool,
    want: &'s str,
    src: &'s str,
}

fn report(index: usize, case: Case<'_>, samples: &mut Samples, check: bool) {
    for v in [&mut samples.parse, &mut samples.lower, &mut samples.total] {
        v.sort_by(f64::total_cmp);
    }
    let src = case.src;
    let r = engine::evaluate(src).expect("a golden case parses");
    let got = if case.mutation { r.mutation.to_string() } else { r.verdict.to_string() };
    assert_eq!(got, case.want, "{src}");
    assert!(r.saturated && r.consistent, "{src}");
    let (p, l, t) = (&samples.parse, &samples.lower, &samples.total);
    if check {
        assert!(quantile(p, 95) < 50.0, "parser p95 exceeded 50 us: {src}");
        assert!(quantile(l, 95) < 50.0, "parser + lowering p95 exceeded 50 us: {src}");
        assert!(quantile(t, 95) < 1000.0, "end-to-end p95 exceeded 1 ms: {src}");
        assert!(r.nodes < 150, "graph exceeded 149 nodes: {src}");
    }
    println!(
        "{index}\t{:.1}/{:.1}\t{:.1}/{:.1}\t{:.1}/{:.1}/{:.1}/{:.1}\t{}\t{}",
        quantile(p, 50),
        quantile(p, 95),
        quantile(l, 50),
        quantile(l, 95),
        quantile(t, 50),
        quantile(t, 95),
        quantile(t, 99),
        t[t.len() - 1],
        r.nodes,
        r.iterations
    );
}

fn main() {
    let count: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(200);
    let check = std::env::args().any(|s| s == "--check");
    let start = Instant::now();
    engine::initialize();
    println!("runtime initialization: {:.1} us", micros(start));
    let golden = |text: &'static str, mutation: bool| {
        text.lines()
            .filter(|l| !l.starts_with('#') && !l.is_empty())
            .filter_map(|l| l.split_once('\t'))
            .map(move |(want, src)| Case { mutation, want, src })
    };
    let cases: Vec<Case<'_>> = golden(include_str!("../tests/cases.txt"), false).chain(golden(include_str!("../tests/mutations.txt"), true)).collect();
    let cold = engine::evaluate(cases[0].src).expect("a golden case parses");
    println!(
        "first evaluation after runtime init: {:.1} us total, {:.1} us parse/lower",
        cold.total_time.as_secs_f64() * 1e6,
        cold.parse_time.as_secs_f64() * 1e6
    );
    for case in &cases {
        for _ in 0..5 {
            black_box(engine::evaluate(case.src).ok());
        }
    }
    // Interleave inputs so later cases do not systematically receive a warmer CPU.
    let mut samples = vec![Samples::default(); cases.len()];
    for _ in 0..count.max(1) {
        for (case, into) in cases.iter().zip(&mut samples) {
            sample(case.src, into);
        }
    }
    println!("case\tparse p50/p95 us\tlower p50/p95 us\ttotal p50/p95/p99/max us\tnodes\titers");
    for (i, (case, into)) in cases.iter().zip(&mut samples).enumerate() {
        report(i + 1, *case, into, check);
    }
}
