//! Command-line probe: `omelette '<expr>' [--all]` or `omelette --joint [--json] '<a>' '<b>' ...`.
use egg::{Language, RecExpr};
use omelette::core::Core;
use omelette::engine::{Evaluation, JointEvaluation, Mutation, evaluate, evaluate_joint, initialize};
use std::fmt::Write as _;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let all = args.iter().any(|s| s == "--all");
    let joint = args.iter().any(|s| s == "--joint");
    let json = args.iter().any(|s| s == "--json");
    let exprs: Vec<&str> = args.iter().filter(|s| !s.starts_with("--")).map(String::as_str).collect();
    initialize();
    if joint {
        return print_joint(&exprs, json);
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
    // The term shares subterms; written out as a tree it can be exponentially larger.
    if tree_size(&r.canonical) <= 1 << 16 {
        println!("root: {}", r.canonical);
    } else {
        println!("root: <a term of {} shared nodes, too large to write as a tree>", r.canonical.len());
    }
    println!("consistency: {}", consistency(r.consistent));
    if r.opaque {
        println!("opaque: yes (the root assumes what lowering does not model)");
    }
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

fn print_joint(exprs: &[&str], json: bool) -> ExitCode {
    match evaluate_joint(exprs) {
        Ok(r) if json => {
            println!("{}", joint_json(&r));
            ExitCode::SUCCESS
        }
        Ok(r) => {
            println!("joint: {} iterations, {} e-nodes, saturated: {}", r.iterations, r.nodes, r.saturated);
            println!("consistency: {}", consistency(r.consistent));
            for (((src, id), term), opaque) in exprs.iter().zip(&r.roots).zip(&r.canonical).zip(&r.opaque) {
                let note = if *opaque { " (opaque: the root assumes what lowering does not model)" } else { "" };
                println!("c{id}: {src}{note}\n  {term}");
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("parse error: {e}");
            ExitCode::FAILURE
        }
    }
}

/// The joint run as JSON: its soundness, each root's class, and each root's term as a list
/// of nodes, each its operator (or datum) and its children's positions in that list.
fn joint_json(r: &JointEvaluation) -> String {
    let roots: Vec<String> = r.roots.iter().map(ToString::to_string).collect();
    let opaque: Vec<String> = r.opaque.iter().map(ToString::to_string).collect();
    let terms: Vec<String> = r.canonical.iter().map(term_json).collect();
    format!(
        "{{\"saturated\":{},\"consistent\":{},\"roots\":[{}],\"opaque\":[{}],\"terms\":[{}]}}",
        r.saturated,
        r.consistent,
        roots.join(","),
        opaque.join(","),
        terms.join(",")
    )
}

fn term_json(term: &RecExpr<Core>) -> String {
    let nodes: Vec<String> = term
        .as_ref()
        .iter()
        .map(|node| {
            let children: Vec<String> = node.children().iter().map(|&c| usize::from(c).to_string()).collect();
            format!("[{},[{}]]", json_string(&node.to_string()), children.join(","))
        })
        .collect();
    format!("[{}]", nodes.join(","))
}

fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if u32::from(c) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn consistency(consistent: bool) -> &'static str {
    if consistent { "ok" } else { "inconsistent" }
}

/// How many nodes a term has written out as a tree, saturating.
fn tree_size(term: &RecExpr<Core>) -> usize {
    let mut sizes: Vec<usize> = Vec::with_capacity(term.len());
    for node in term.as_ref() {
        let size = node.children().iter().fold(1_usize, |total, &c| total.saturating_add(sizes[usize::from(c)]));
        sizes.push(size);
    }
    sizes.last().copied().unwrap_or(0)
}
