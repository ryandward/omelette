// TS expression -> (frontend/dump.ts) S-expression -> egglog saturation -> cheat query.
// egglog owns the e-graph, the rule matching (multi-pattern joins are plain rules) and the
// analyses (lo/hi/free are functions with lattice merges). This file declares the constructors,
// generates the rules that are the same for every constructor (free variables, let-pushing),
// translates the dumper's output into terms, runs to saturation, and reads the result back.
use egglog::{CommandOutput, EGraph, SerializeConfig};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::process::Command;
use std::time::{Duration, Instant};

const RULES: &str = include_str!("../rules.egg");
const ITER_LIMIT: usize = 60;
const TIME_LIMIT: Duration = Duration::from_secs(20);
const NODE_LIMIT: usize = 60_000;

// Every constructor of T: name, argument sorts, and whether it is source syntax (which costs 1000
// in extraction, so it survives in the cheapest reading only where no rule gave it a meaning).
const CTORS: &[(&str, &[&str], bool)] = &[
    ("Num", &["i64"], false), ("B", &["bool"], false), ("Undef", &[], false), ("Nil", &[], false),
    ("Oob", &[], false), ("Throw", &[], false),
    ("Var", &["String"], false), ("Lam", &["String", "T"], false), ("Let", &["String", "T", "T"], false),
    ("Add", &["T", "T"], false), ("Sub", &["T", "T"], false), ("Mul", &["T", "T"], false), ("Neg", &["T"], false),
    ("Lt", &["T", "T"], false), ("Le", &["T", "T"], false), ("EqI", &["T", "T"], false), ("StrictEq", &["T", "T"], false),
    ("Not", &["T"], false), ("And", &["T", "T"], false), ("Or", &["T", "T"], false), ("If", &["T", "T", "T"], false),
    ("Min", &["T", "T"], false), ("Max", &["T", "T"], false),
    ("Len", &["T"], false), ("IndexQ", &["T", "T"], false), ("At", &["T", "T"], false), ("Cons", &["T", "T"], false),
    ("Append", &["T", "T"], false), ("Sublist", &["T", "T", "T"], false), ("Rel", &["T", "T"], false),
    ("Map", &["T", "T"], false), ("Reverse", &["T"], false), ("Foldl", &["T", "T", "T"], false),
    ("Filteri", &["T", "T", "T"], false), ("Maybe", &["T", "T"], false),
    ("Prop", &["T", "String"], true), ("Elem", &["T", "T"], true), ("MCall0", &["String", "T"], true),
    ("MCall1", &["String", "T", "T"], true), ("MCall2", &["String", "T", "T", "T"], true), ("App", &["T", "T"], true),
    ("Truthy", &["T"], true), ("Coalesce", &["T", "T"], true), ("Default", &["T", "T"], true),
    ("ArrCons", &["T", "T"], true), ("ArrSpread", &["T", "T"], true), ("Unknown", &["String"], true),
];
// Constructors whose free-variable and let rules are written by hand.
const BINDERS: [&str; 3] = ["Var", "Lam", "Let"];

fn prelude() -> String {
    let mut p = String::from("(sort T)\n(sort TS (MultiSet T))\n(sort StrSet (Set String))\n(sort TFn (UnstableFn (T) T))\n(sort IS (MultiSet i64))\n(sort TIFn (UnstableFn (T) i64))\n(sort IIFn (UnstableFn (i64 i64) i64))\n");
    for (name, args, syntax) in CTORS {
        let cost = if *syntax { " :cost 1000" } else { "" };
        p += &format!("(constructor {name} ({}) T{cost})\n", args.join(" "));
    }
    p += "(constructor Lin (TS) T :cost 100)\n(constructor RootOf (i64) T :cost 1000000)\n";
    p += "(function linr (T i64) TS :merge (ordering-min old new))\n(function linrank (T) i64 :merge (max old new))\n";
    p += "(function free (T) StrSet :merge (set-intersect old new))\n";
    p += "(function lo (T) i64 :merge (max old new))\n(function hi (T) i64 :merge (min old new))\n";
    p += "(relation IsInt (T))\n(relation Clash (T))\n";
    // Depth: leaves 0, any other e-node one more than its deepest T child, merged by min. The
    // affine flattening only pulls a shallower class into a deeper one, which is what makes it stop
    // on classes defined through each other (a = x + b beside x = a - b).
    p += "(function depth (T) i64 :merge (min old new))\n";
    for (name, args, _) in CTORS {
        let vars: Vec<String> = (0..args.len()).map(|i| format!("a{i}")).collect();
        let ts: Vec<usize> = (0..args.len()).filter(|&i| args[i] == "T").collect();
        let pat = if args.is_empty() { format!("({name})") } else { format!("({name} {})", vars.join(" ")) };
        let mut q = format!("(= x {pat})");
        for &i in &ts { q += &format!(" (= d{i} (depth a{i}))"); }
        let val = match ts.as_slice() {
            [] => "0".to_string(),
            _ => format!("(+ 1 {})", ts[1..].iter().fold(format!("d{}", ts[0]), |acc, i| format!("(max {acc} d{i})"))),
        };
        p += &format!("(rule ({q}) ((set (depth x) {val})) :name \"depth-{name}\")\n");
    }
    // Free variables: a constructor's are its T children's; the binders are by hand.
    p += "(rule ((= x (Var s))) ((set (free x) (set-of s))) :name \"free-Var\")\n";
    p += "(rule ((= x (Lam s b)) (= fb (free b))) ((set (free x) (set-remove fb s))) :name \"free-Lam\")\n";
    p += "(rule ((= x (Let s e b)) (= fb (free b)) (= fe (free e))) ((set (free x) (set-union (set-remove fb s) fe))) :name \"free-Let\")\n";
    for (name, args, _) in CTORS {
        if BINDERS.contains(name) { continue; }
        let vars: Vec<String> = (0..args.len()).map(|i| format!("a{i}")).collect();
        let ts: Vec<usize> = (0..args.len()).filter(|&i| args[i] == "T").collect();
        let pat = if args.is_empty() { format!("({name})") } else { format!("({name} {})", vars.join(" ")) };
        let mut q = format!("(= x {pat})");
        for &i in &ts { q += &format!(" (= f{i} (free a{i}))"); }
        let val = match ts.as_slice() {
            [] => "(set-empty)".to_string(),
            [i] => format!("f{i}"),
            _ => ts[1..].iter().fold(format!("f{}", ts[0]), |acc, i| format!("(set-union {acc} f{i})")),
        };
        p += &format!("(rule ({q}) ((set (free x) {val})) :name \"free-{name}\")\n");
        // (Let v e (Op ..)) pushes the let into every T child, when v is free in the body.
        if ts.is_empty() { continue; }
        let pushed: Vec<String> = (0..args.len()).map(|i| if args[i] == "T" { format!("(Let v e a{i})") } else { format!("a{i}") }).collect();
        p += &format!("(rule ((= x (Let v e body)) (= body {pat}) (= fb (free body)) (set-contains fb v)) ((union x ({name} {}))) :name \"let-{name}\")\n", pushed.join(" "));
    }
    p
}

// --- the dumper's S-expression, read and translated into T terms ---
enum Sx { Atom(String), List(Vec<Sx>) }
fn parse(s: &str) -> Sx {
    let mut toks: VecDeque<String> = VecDeque::new();
    let cs: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < cs.len() {
        match cs[i] {
            '(' | ')' => { toks.push_back(cs[i].to_string()); i += 1; }
            c if c.is_whitespace() => i += 1,
            '"' => { let j = (i + 1..cs.len()).find(|&j| cs[j] == '"').unwrap_or(cs.len() - 1); toks.push_back(cs[i + 1..j].iter().collect()); i = j + 1; }
            _ => { let j = (i..cs.len()).find(|&j| cs[j] == '(' || cs[j] == ')' || cs[j].is_whitespace()).unwrap_or(cs.len()); toks.push_back(cs[i..j].iter().collect()); i = j; }
        }
    }
    fn go(t: &mut VecDeque<String>) -> Sx {
        let tok = t.pop_front().unwrap_or_default();
        if tok != "(" { return Sx::Atom(tok); }
        let mut xs = vec![];
        while t.front().map_or(false, |x| x != ")") { xs.push(go(t)); }
        t.pop_front();
        Sx::List(xs)
    }
    go(&mut toks)
}
fn quote(s: &str) -> String { format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "'")) }
fn name(x: &Sx) -> String { match x { Sx::Atom(a) => a.clone(), Sx::List(_) => "?".into() } }
fn term(x: &Sx) -> String {
    let xs = match x {
        Sx::Atom(a) => return match a.as_str() {
            "undef" => "(Undef)".into(), "nil" => "(Nil)".into(), "true" => "(B true)".into(), "false" => "(B false)".into(),
            _ => match a.parse::<i64>() { Ok(v) => format!("(Num {v})"), Err(_) => format!("(Unknown {})", quote(a)) },
        },
        Sx::List(xs) => xs,
    };
    let op = name(&xs[0]);
    let t = |i: usize| term(&xs[i]);
    let bin = |c: &str| format!("({c} {} {})", t(1), t(2));
    match (op.as_str(), xs.len()) {
        ("var", 2) => format!("(Var {})", quote(&name(&xs[1]))),
        ("lam", 3) => format!("(Lam {} {})", quote(&name(&xs[1])), t(2)),
        ("let", 4) => format!("(Let {} {} {})", quote(&name(&xs[1])), t(2), t(3)),
        ("+", 3) => bin("Add"), ("-", 3) => bin("Sub"), ("*", 3) => bin("Mul"), ("<", 3) => bin("Lt"), ("<=", 3) => bin("Le"),
        ("===", 3) => bin("StrictEq"), ("&&", 3) => bin("And"), ("||", 3) => bin("Or"), ("coalesce", 3) => bin("Coalesce"),
        ("default", 3) => bin("Default"), ("elem", 3) => bin("Elem"), ("app", 3) => bin("App"),
        ("arr-cons", 3) => bin("ArrCons"), ("arr-spread", 3) => bin("ArrSpread"),
        ("neg", 2) => format!("(Neg {})", t(1)), ("!", 2) => format!("(Not {})", t(1)), ("truthy", 2) => format!("(Truthy {})", t(1)),
        ("if", 4) => format!("(If {} {} {})", t(1), t(2), t(3)),
        ("prop", 3) => format!("(Prop {} {})", t(1), quote(&name(&xs[2]))),
        ("mcall", n) if (3..=5).contains(&n) => format!("(MCall{} {} {})", n - 3, quote(&name(&xs[1])), (2..n).map(t).collect::<Vec<_>>().join(" ")),
        ("unknown", 2) => format!("(Unknown {})", quote(&name(&xs[1]))),
        _ => format!("(Unknown {})", quote(&format!("{op}/{}", xs.len() - 1))),
    }
}
fn dump(src: &str) -> Result<String, String> {
    let out = Command::new("node").arg(concat!(env!("CARGO_MANIFEST_DIR"), "/frontend/dump.ts")).arg(src).output().map_err(|e| e.to_string())?;
    let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if s.is_empty() { Err(String::from_utf8_lossy(&out.stderr).to_string()) } else { Ok(s) }
}

// --- the saturated e-graph, read back as classes of e-nodes ---
struct Graph { ops: Vec<String>, kids: Vec<Vec<usize>>, class_of: Vec<usize>, classes: BTreeMap<usize, Vec<usize>>, lo: HashMap<usize, i64>, hi: HashMap<usize, i64>, clash: Vec<usize>, roots: Vec<usize> }
impl Graph {
    fn read(eg: &EGraph, n_roots: usize) -> Graph {
        let s = eg.serialize(SerializeConfig::default()).egraph;
        let ids: HashMap<_, usize> = s.nodes.keys().enumerate().map(|(i, k)| (k.clone(), i)).collect();
        let cids: HashMap<_, usize> = { let mut m = HashMap::new(); for n in s.nodes.values() { let l = m.len(); m.entry(n.eclass.clone()).or_insert(l); } m };
        let ops: Vec<String> = s.nodes.values().map(|n| n.op.clone()).collect();
        let kids: Vec<Vec<usize>> = s.nodes.values().map(|n| n.children.iter().map(|c| ids[c]).collect()).collect();
        let class_of: Vec<usize> = s.nodes.values().map(|n| cids[&n.eclass]).collect();
        let (mut classes, mut lo, mut hi, mut clash, mut roots) = (BTreeMap::<usize, Vec<usize>>::new(), HashMap::new(), HashMap::new(), vec![], vec![usize::MAX; n_roots]);
        let num = |i: usize| ops[i].parse::<i64>().ok();
        let val: HashMap<usize, i64> = (0..ops.len()).filter_map(|i| Some((class_of[i], num(i)?))).collect();
        for i in 0..ops.len() {
            match ops[i].as_str() {
                "lo" | "hi" => {
                    // A function row: its child is the argument, its own class is the value's.
                    if let Some(&v) = val.get(&class_of[i]) { if ops[i] == "lo" { lo.insert(class_of[kids[i][0]], v); } else { hi.insert(class_of[kids[i][0]], v); } }
                }
                "Clash" => clash.push(class_of[kids[i][0]]),
                "RootOf" => if let Some(k) = num(kids[i][0]) { if (k as usize) < n_roots { roots[k as usize] = class_of[i]; } },
                "free" | "IsInt" | "depth" | "linr" | "linrank" | "Shallow" => {}
                _ => classes.entry(class_of[i]).or_default().push(i),
            }
        }
        Graph { ops, kids, class_of, classes, lo, hi, clash, roots }
    }
    fn is_ctor(&self, i: usize) -> bool { let o = self.ops[i].as_str(); o == "Lin" || CTORS.iter().any(|(n, _, _)| *n == o) }
    fn has(&self, c: usize, op: &str) -> bool { self.classes.get(&c).map_or(false, |ns| ns.iter().any(|&i| self.ops[i] == op)) }
    fn kid(&self, i: usize, k: usize) -> usize { self.class_of[self.kids[i][k]] }
    fn reachable(&self, from: &[usize]) -> Vec<usize> {
        let mut seen = HashSet::new();
        let mut stack: Vec<usize> = from.to_vec();
        let mut order = vec![];
        while let Some(c) = stack.pop() {
            if !seen.insert(c) { continue; }
            order.push(c);
            for &i in self.classes.get(&c).into_iter().flatten() { for &k in &self.kids[i] { stack.push(self.class_of[k]); } }
        }
        order.sort();
        order
    }
    // Cheapest term per class, source syntax costing 1000 and RootOf 10^6.
    fn extract(&self) -> HashMap<usize, (u64, String)> {
        let mut best: HashMap<usize, (u64, String)> = HashMap::new();
        loop {
            let mut changed = false;
            for (&c, ns) in &self.classes {
                for &i in ns {
                    let own: u64 = match self.ops[i].as_str() { "RootOf" => 1_000_000, o if CTORS.iter().any(|(n, _, s)| *n == o && *s) => 1000, _ => 1 };
                    let ks: Option<Vec<&(u64, String)>> = self.kids[i].iter().map(|k| best.get(&self.class_of[*k])).collect();
                    let Some(ks) = ks else { continue };
                    let cost = ks.iter().fold(own, |a, k| a.saturating_add(k.0));
                    if best.get(&c).map_or(true, |b| cost < b.0) {
                        let s = if ks.is_empty() { if self.is_ctor(i) { format!("({})", self.ops[i]) } else { self.ops[i].clone() } } else { format!("({} {})", self.ops[i], ks.iter().map(|k| k.1.as_str()).collect::<Vec<_>>().join(" ")) };
                        best.insert(c, (cost, s));
                        changed = true;
                    }
                }
            }
            if !changed { return best; }
        }
    }
}
struct Run { eg: EGraph, iters: usize, saturated: bool, why: String, ms: f64 }
fn saturate(terms: &[String]) -> Result<Run, String> {
    let mut eg = EGraph::default();
    let mut prog = prelude() + RULES;
    // (Neg (Num 1)) exists so a -1 unit in a form can cancel against a +1.
    prog += "\n(Neg (Num 1))";
    for (k, t) in terms.iter().enumerate() { prog += &format!("\n(union (RootOf {k}) {t})"); }
    eg.parse_and_run_program(None, &prog).map_err(|e| e.to_string())?;
    let start = Instant::now();
    let (mut iters, mut saturated, mut why) = (0, false, String::new());
    let limit: usize = std::env::var("ITERS").ok().and_then(|v| v.parse().ok()).unwrap_or(ITER_LIMIT);
    while iters < limit {
        let out = eg.parse_and_run_program(None, "(run 1)").map_err(|e| e.to_string())?;
        iters += 1;
        if std::env::var("TRACE").is_ok() {
            let mut top: Vec<(String, usize)> = out.iter().filter_map(|o| if let CommandOutput::RunSchedule(r) = o { Some(r.num_matches_per_rule.iter().map(|(k, v)| (k.to_string(), *v)).collect::<Vec<_>>()) } else { None }).flatten().filter(|x| x.1 > 0).collect();
            top.sort_by(|a, b| b.1.cmp(&a.1));
            eprintln!("  iter {iters}: {} tuples, {:.1} ms  {}", eg.num_tuples(), start.elapsed().as_secs_f64() * 1e3, top.iter().take(8).map(|(k, v)| format!("{k} x{v}")).collect::<Vec<_>>().join(", "));
        }
        let updated = out.iter().any(|o| matches!(o, CommandOutput::RunSchedule(r) if r.updated));
        if !updated { saturated = true; break; }
        if start.elapsed() > TIME_LIMIT { why = "TimeLimit".into(); break; }
        if eg.num_tuples() > NODE_LIMIT { why = "NodeLimit".into(); break; }
    }
    if !saturated && why.is_empty() { why = "IterationLimit".into(); }
    Ok(Run { eg, iters, saturated, why, ms: start.elapsed().as_secs_f64() * 1e3 })
}

const SYNTAX: [&str; 12] = ["Prop", "Elem", "MCall0", "MCall1", "MCall2", "App", "Truthy", "Coalesce", "Default", "ArrCons", "ArrSpread", "Unknown"];

fn stats(g: &Graph) -> (usize, usize) {
    let nodes = g.classes.values().flatten().filter(|&&i| g.is_ctor(i)).count();
    let classes = g.classes.iter().filter(|(_, ns)| ns.iter().any(|&i| g.is_ctor(i))).count();
    (nodes, classes)
}

fn run_one(src: &str, show_all: bool) {
    println!("\n{}\n{src}", "=".repeat(100));
    let sexpr = match dump(src) { Ok(s) => s, Err(e) => { println!("dumper failed: {e}"); return; } };
    println!("dumped:  {sexpr}");
    let t = term(&parse(&sexpr));
    let r = match saturate(&[t]) { Ok(r) => r, Err(e) => { println!("egglog error: {e}"); return; } };
    let g = Graph::read(&r.eg, 1);
    let (nodes, classes) = stats(&g);
    println!("egglog:  {} iterations, {nodes} e-nodes, {classes} e-classes, {:.1} ms, stop: {}", r.iters, r.ms, if r.saturated { "Saturated".into() } else { r.why.clone() });
    let best = g.extract();
    let root = g.roots[0];
    let show = |c: usize| best.get(&c).map_or(format!("c{c}"), |b| b.1.clone());
    println!("root:    {}", show(root));
    let order = g.reachable(&[root]);
    let mut hits = vec![];
    for &c in &order {
        for &i in &g.classes[&c] {
            if g.ops[i] != "Maybe" { continue; }
            let (z, m) = (g.kid(i, 0), g.kid(i, 1));
            let born = g.has(m, "IndexQ");
            let determined = ["Undef", "At", "Oob", "Num", "B"].iter().any(|o| g.has(m, o));
            let written = !["Undef", "Oob", "Throw"].iter().any(|o| g.has(z, o));
            if born && !determined && written { hits.push(format!("e-class {c}: (Maybe {} {})", show(z), show(m))); }
        }
    }
    let reading = show(root);
    let opaque: Vec<&str> = SYNTAX.iter().copied().filter(|s| reading.contains(&format!("({s} "))).collect();
    let unknown = reading.contains("(Unknown ");
    let clash: Vec<usize> = g.clash.iter().copied().filter(|c| order.contains(c)).collect();
    println!("consistency: {}", if g.clash.is_empty() { "ok".to_string() } else { format!("UNSOUND, Clash in {:?} ({} under the root)", g.clash, clash.len()) });
    if std::env::var("RANKDBG").is_ok() {
        for i in 0..g.ops.len() { if g.ops[i] == "linrank" { let v = g.ops.iter().enumerate().find(|(j, o)| g.class_of[*j] == g.class_of[i] && o.parse::<i64>().is_ok()).map(|(_, o)| o.clone()); println!("  linrank c{} = {:?}  {}", g.class_of[g.kids[i][0]], v, show(g.class_of[g.kids[i][0]])); } }
    }
    if std::env::var("CLASHDBG").is_ok() { let mut cs = g.clash.clone(); cs.sort(); cs.dedup(); print_classes(&g, &best, &cs, root); }
    if !hits.is_empty() {
        println!("verdict: CHEAT");
        for h in hits.iter().take(4) { println!("  {h}"); }
    } else if unknown {
        println!("verdict: UNDECIDED (an unknown syntax form is under the root)");
    } else if !opaque.is_empty() {
        println!("verdict: UNDECIDED (no rule gives a meaning to {})", opaque.join(", "));
    } else if !r.saturated {
        println!("verdict: UNDECIDED (stopped at a limit before saturating; no finding yet)");
    } else {
        println!("verdict: no cheat");
    }
    if show_all { print_classes(&g, &best, &order, root); }
}

fn print_classes(g: &Graph, best: &HashMap<usize, (u64, String)>, order: &[usize], root: usize) {
    println!("e-classes reachable from the root ({}):", order.len());
    for &c in order {
        let ns: Vec<String> = g.classes[&c].iter().map(|&i| if g.kids[i].is_empty() { g.ops[i].clone() } else { format!("({} {})", g.ops[i], g.kids[i].iter().map(|k| format!("c{}", g.class_of[*k])).collect::<Vec<_>>().join(" ")) }).collect();
        let iv = match (g.lo.get(&c), g.hi.get(&c)) { (None, None) => String::new(), (l, h) => format!("  in [{}, {}]", l.map_or("-inf".into(), |v| v.to_string()), h.map_or("+inf".into(), |v| v.to_string())) };
        println!("  {}c{c}{iv}  best {}\n      {}", if c == root { "*" } else { " " }, best.get(&c).map_or("?", |b| b.1.as_str()), ns.join("\n      "));
    }
}

fn joint(srcs: &[String]) {
    let terms: Vec<String> = srcs.iter().map(|s| term(&parse(&dump(s).expect("dump")))).collect();
    let r = match saturate(&terms) { Ok(r) => r, Err(e) => { println!("egglog error: {e}"); return; } };
    let g = Graph::read(&r.eg, srcs.len());
    let (nodes, classes) = stats(&g);
    println!("one e-graph, {} roots: {} iterations, {nodes} e-nodes, {classes} e-classes, {:.1} ms, stop: {}", srcs.len(), r.iters, r.ms, if r.saturated { "Saturated".into() } else { r.why.clone() });
    println!("consistency: {}", if g.clash.is_empty() { "ok".to_string() } else { format!("UNSOUND, Clash in {:?}", g.clash) });
    let best = g.extract();
    println!("\nroots:");
    for (src, r) in srcs.iter().zip(&g.roots) { println!("  c{r}  <- {src}"); }
    let mut seen = HashSet::new();
    for &r in &g.roots {
        if !seen.insert(r) { continue; }
        let members: Vec<usize> = g.roots.iter().enumerate().filter(|(_, x)| **x == r).map(|(i, _)| i + 1).collect();
        println!("\ne-class c{r} holds roots {members:?}: best {}", best.get(&r).map_or("?", |b| b.1.as_str()));
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--prelude") { print!("{}{}", prelude(), RULES); return; }
    // --egg FILE: run a raw egglog program (for checking a primitive's behaviour).
    if let Some(i) = args.iter().position(|a| a == "--egg") {
        let src = std::fs::read_to_string(&args[i + 1]).expect("read");
        let mut eg = EGraph::default();
        match eg.parse_and_run_program(None, &src) { Ok(out) => for o in out { println!("{o}"); }, Err(e) => println!("error: {e}") }
        return;
    }
    let show_all = args.iter().any(|a| a == "--all");
    let exprs: Vec<String> = args.iter().filter(|a| !a.starts_with("--")).cloned().collect();
    if args.iter().any(|a| a == "--joint") { joint(&exprs); return; }
    let defaults = [
        "widths.slice(i, i + 1).reduce((_, x) => x, 0)",
        "widths.slice(i, i + 1).reduce((acc, x) => x + (acc - acc), 0)",
        "(([x = 0]) => x)(widths.slice(i, i + 1))",
        "[0, ...xs][xs.length]",
        "widths.reduce((a, b) => a + b, 0)",
        "widths.reduce((a, b) => a + b, 0) + widths.length",
    ];
    if exprs.is_empty() { for e in defaults { run_one(e, false); } } else { for e in &exprs { run_one(e, show_all); } }
}
