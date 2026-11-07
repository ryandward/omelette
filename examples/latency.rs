//! Run with `cargo run --release --example latency -- 200`.
use omelette::{engine, frontend};
use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_span::SourceType;
use std::{hint::black_box, time::Instant};
fn quantile(v: &[f64], p: f64) -> f64 {
    v[((v.len() - 1) as f64 * p).ceil() as usize]
}
fn main() {
    let count: usize = std::env::args()
        .nth(1)
        .map(|s| s.parse().unwrap())
        .unwrap_or(200);
    assert!(count > 0);
    let check = std::env::args().any(|s| s == "--check");
    let start = Instant::now();
    engine::initialize();
    println!(
        "runtime initialization: {:.1} us",
        start.elapsed().as_secs_f64() * 1e6
    );
    let cases: Vec<_> = include_str!("../tests/cases.txt")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .map(|l| l.split_once('\t').unwrap())
        .collect();
    let cold = engine::evaluate(cases[0].1).unwrap();
    println!(
        "first evaluation after runtime init: {:.1} us total, {:.1} us parse/lower",
        cold.total_time.as_secs_f64() * 1e6,
        cold.parse_time.as_secs_f64() * 1e6
    );
    drop(cold);
    let mut timings = vec![(vec![], vec![], vec![]); cases.len()];
    for (_, src) in &cases {
        for _ in 0..5 {
            black_box(engine::evaluate(src).unwrap());
        }
    }
    // Interleave inputs so later cases do not systematically receive a warmer CPU.
    for _ in 0..count {
        for (i, (_, src)) in cases.iter().enumerate() {
            let start = Instant::now();
            {
                let arena = Allocator::default();
                black_box(
                    Parser::new(&arena, black_box(src), SourceType::ts())
                        .parse_expression()
                        .unwrap(),
                );
            }
            timings[i].0.push(start.elapsed().as_secs_f64() * 1e6);
            let start = Instant::now();
            black_box(frontend::parse(black_box(src)).unwrap());
            timings[i].1.push(start.elapsed().as_secs_f64() * 1e6);
            let start = Instant::now();
            let result = engine::evaluate(black_box(src)).unwrap();
            black_box(&result);
            drop(result);
            timings[i].2.push(start.elapsed().as_secs_f64() * 1e6);
        }
    }
    println!("case\tparse p50/p95 us\tlower p50/p95 us\ttotal p50/p95/p99/max us\tnodes\titers");
    for (i, ((want, src), (p, l, t))) in cases.iter().zip(timings.iter_mut()).enumerate() {
        for v in [&mut *p, &mut *l, &mut *t] {
            v.sort_by(f64::total_cmp);
        }
        let r = engine::evaluate(src).unwrap();
        assert_eq!(r.verdict.to_string(), *want, "{src}");
        assert!(r.saturated && r.consistent, "{src}");
        if check {
            assert!(quantile(p, 0.95) < 50.0, "parser p95 exceeded 50 us: {src}");
            assert!(
                quantile(l, 0.95) < 50.0,
                "parser + lowering p95 exceeded 50 us: {src}"
            );
            assert!(
                quantile(t, 0.95) < 1000.0,
                "end-to-end p95 exceeded 1 ms: {src}"
            );
            assert!(r.nodes < 150, "graph exceeded 149 nodes: {src}");
        }
        println!(
            "{}\t{:.1}/{:.1}\t{:.1}/{:.1}\t{:.1}/{:.1}/{:.1}/{:.1}\t{}\t{}",
            i + 1,
            quantile(p, 0.5),
            quantile(p, 0.95),
            quantile(l, 0.5),
            quantile(l, 0.95),
            quantile(t, 0.5),
            quantile(t, 0.95),
            quantile(t, 0.99),
            t.last().unwrap(),
            r.nodes,
            r.iterations
        );
    }
}
