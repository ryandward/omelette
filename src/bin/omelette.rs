use omelette::engine::{evaluate, initialize};
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let all = args.iter().any(|s| s == "--all");
    let joint = args.iter().any(|s| s == "--joint");
    let mut exprs: Vec<_> = args
        .iter()
        .filter(|s| !s.starts_with("--"))
        .map(String::as_str)
        .collect();
    if exprs.is_empty() {
        exprs = vec![
            "widths.slice(i, i + 1).reduce((_, x) => x, 0)",
            "widths.slice(i, i + 2).reduce((a, b) => a + b, 0)",
        ];
    }
    initialize();
    if joint {
        match omelette::engine::evaluate_joint(&exprs) {
            Ok(r) => {
                println!(
                    "joint: {} iterations, {} e-nodes, saturated: {}",
                    r.iterations, r.nodes, r.saturated
                );
                for ((src, id), term) in exprs.iter().zip(r.roots).zip(r.canonical) {
                    println!("c{id}: {src}\n  {term}");
                }
            }
            Err(e) => {
                eprintln!("parse error: {e}");
                std::process::exit(1);
            }
        }
        return;
    }
    let mut failed = false;
    for src in exprs {
        println!("\n{src}");
        match evaluate(src) {
            Err(e) => {
                println!("verdict: UNDECIDED (parse error: {e})");
                failed = true;
            }
            Ok(r) => {
                println!(
                    "egg: {} iterations, {} e-nodes, {} e-classes, {:.3} ms total, {:.1} us parse/lower, stop: {}",
                    r.iterations,
                    r.nodes,
                    r.classes,
                    r.total_time.as_secs_f64() * 1000.0,
                    r.parse_time.as_secs_f64() * 1e6,
                    r.stop
                );
                println!("root: {}", r.canonical);
                println!(
                    "consistency: {}",
                    if r.consistent { "ok" } else { "UNSOUND" }
                );
                println!("verdict: {}", r.verdict);
                if all {
                    for c in r.graph.classes() {
                        println!("{} {:?} {:?}", c.id, c.data, c.nodes);
                    }
                }
            }
        }
    }
    if failed {
        std::process::exit(1);
    }
}
