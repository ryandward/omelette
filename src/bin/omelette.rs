//! Command-line probe: `omelette '<expr>' [--all]` or `omelette --joint '<a>' '<b>' ...`.
use omelette::engine::{Evaluation, Mutation, evaluate, evaluate_joint, initialize};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let all = args.iter().any(|s| s == "--all");
    let joint = args.iter().any(|s| s == "--joint");
    let exprs: Vec<&str> = args.iter().filter(|s| !s.starts_with("--")).map(String::as_str).collect();
    initialize();
    if joint {
        return print_joint(&exprs);
    }
    let mut status = ExitCode::SUCCESS;
    for src in exprs {
        println!("\n{src}");
        match evaluate(src) {
            Ok(r) => print(&r, all),
            Err(e) => {
                println!("verdict: UNDECIDED (parse error: {e})");
                status = ExitCode::FAILURE;
            }
        }
    }
    status
}

fn print(r: &Evaluation, all: bool) {
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
    println!("consistency: {}", consistency(r.consistent));
    let families: Vec<String> = r.families.iter().map(ToString::to_string).collect();
    if families.is_empty() {
        println!("verdict: {}", r.verdict);
    } else {
        println!("verdict: {} ({})", r.verdict, families.join(", "));
    }
    match &r.mutation {
        Mutation::Observable(ops) => {
            let names: Vec<&str> = ops.iter().map(|m| m.name()).collect();
            println!("mutation: {} ({})", r.mutation, names.join(", "));
        }
        m => println!("mutation: {m}"),
    }
    if all {
        for c in r.graph.classes() {
            println!("{} {:?} {:?}", c.id, c.data, c.nodes);
        }
    }
}

fn print_joint(exprs: &[&str]) -> ExitCode {
    match evaluate_joint(exprs) {
        Ok(r) => {
            println!("joint: {} iterations, {} e-nodes, saturated: {}", r.iterations, r.nodes, r.saturated);
            println!("consistency: {}", consistency(r.consistent));
            for ((src, id), term) in exprs.iter().zip(&r.roots).zip(&r.canonical) {
                println!("c{id}: {src}\n  {term}");
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("parse error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn consistency(consistent: bool) -> &'static str {
    if consistent { "ok" } else { "inconsistent" }
}
