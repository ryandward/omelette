//! Latency of the golden cases, absence and mutation. Run with
//! `cargo run --release --example latency -- 500 --check`.
//!
//! `--check` fails on a wrong verdict, an unsaturated or inconsistent graph, a graph of 150
//! e-nodes or more, or, when the host was quiet, a case whose end-to-end p95 reaches the
//! budget. Quiet means other processes used less than one processor's worth of CPU while the
//! samples were taken, as Linux's `/proc` counts it. On a busier host, or one that does not
//! say, the timings are partly the host's, so it judges no latency: it prints why and exits
//! with status 2.
use omelette::{engine, lower};
use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_span::SourceType;
use std::hint::black_box;
use std::time::Instant;

/// The end-to-end p95, in microseconds, the project holds every case under.
const TOTAL_P95_BUDGET_US: f64 = 500.0;

/// How many processors' worth of CPU other processes may use while the samples are taken for
/// the timings to be the code's own. Calibrated on the benchmark host (12 threads) over 45 runs:
/// with other processes under 1.1 processors the worst case's p95 stayed between 397 and
/// 438 us, and from 1.15 up it passed 500 us in most runs. The load average does not show this:
/// it smooths a minute, and a burst inside a run is enough to stretch the tail.
const QUIET_BELOW_PROCESSORS: f64 = 1.0;

/// CPU time spent so far, in clock ticks: by every processor of the machine, busy or idle, by
/// them busy, and by this process.
#[derive(Clone, Copy)]
struct Ticks {
    total: u64,
    busy: u64,
    own: u64,
}

/// The machine's and this process's CPU time, where the system reports them (Linux's `/proc`).
fn ticks() -> Option<Ticks> {
    let stat = std::fs::read_to_string("/proc/stat").ok()?;
    let cpu: Vec<u64> = stat.lines().next()?.split_whitespace().skip(1).map(|f| f.parse().ok()).collect::<Option<_>>()?;
    // user, nice, system, idle, iowait, irq, softirq, steal; guest time is counted in user.
    let total: u64 = cpu.iter().take(8).sum();
    let idle = cpu.get(3)? + cpu.get(4)?;
    // This process's fields after its name: utime and stime are the 12th and 13th.
    let own = std::fs::read_to_string("/proc/self/stat").ok()?;
    let fields: Vec<u64> = own.rsplit_once(')')?.1.split_whitespace().skip(11).take(2).map(|f| f.parse().ok()).collect::<Option<_>>()?;
    Some(Ticks { total, busy: total - idle, own: fields.iter().sum() })
}

/// How many processors' worth of CPU everything but this process used between two readings;
/// `None` where no time passed or the counts do not fit.
fn others(before: Ticks, after: Ticks) -> Option<f64> {
    let total = u32::try_from(after.total.checked_sub(before.total)?).ok().filter(|&t| t > 0)?;
    let busy = after.busy.checked_sub(before.busy)?;
    let own = after.own.checked_sub(before.own)?;
    // This process's ticks are counted apart from the machine's, so over a window its own may
    // exceed what the machine counted busy by a tick: nothing else ran then.
    let busy = u32::try_from(busy.saturating_sub(own)).ok()?;
    let threads = u32::try_from(std::thread::available_parallelism().ok()?.get()).ok()?;
    Some(f64::from(busy) / f64::from(total) * f64::from(threads))
}

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

/// Report one case; under `--check`, assert its verdict and graph, and its end-to-end p95
/// against `budget` where the host allowed timings to be judged.
fn report(index: usize, case: Case<'_>, samples: &mut Samples, check: bool, budget: Option<f64>) {
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
        if let Some(budget) = budget {
            assert!(quantile(t, 95) < budget, "end-to-end p95 reached {budget} us: {src}");
        }
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
    let start = ticks();
    // Interleave inputs so later cases do not systematically receive a warmer CPU.
    let mut samples = vec![Samples::default(); cases.len()];
    for _ in 0..count.max(1) {
        for (case, into) in cases.iter().zip(&mut samples) {
            sample(case.src, into);
        }
    }
    let contention = start.zip(ticks()).and_then(|(a, z)| others(a, z));
    let shown = contention.map_or_else(|| "not measured".to_string(), |o| format!("{o:.2} processors"));
    println!("other processes while sampling: {shown}");
    let quiet = contention.is_some_and(|o| o < QUIET_BELOW_PROCESSORS);
    println!("case\tparse p50/p95 us\tlower p50/p95 us\ttotal p50/p95/p99/max us\tnodes\titers");
    let budget = quiet.then_some(TOTAL_P95_BUDGET_US);
    for (i, (case, into)) in cases.iter().zip(&mut samples).enumerate() {
        report(i + 1, *case, into, check, budget);
    }
    if check && !quiet {
        eprintln!(
            "undecided: other processes used {shown} while sampling, not below {QUIET_BELOW_PROCESSORS:.1}, so the {TOTAL_P95_BUDGET_US} us budget was not judged; rerun on a quiet host"
        );
        std::process::exit(2);
    }
}
