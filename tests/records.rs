//! Declared record types: a field a record type names reads as a value of the field's type,
//! a spread copies those fields, and `Math.max` and `Math.min` choose by order.
mod common;
use common::checked;
use omelette::engine::{Verdict, evaluate, evaluate_joint, initialize};

const ITEM: &str = "type Item = { readonly id: string; readonly k: number; readonly ok: boolean };";

fn with(decls: &str, expr: &str) -> String {
    format!("{ITEM} {decls} {expr}")
}

#[test]
fn a_declared_field_reads_as_its_type() {
    initialize();
    // A number field is an integer atom, so arithmetic on it stays affine.
    let r = checked(&with("declare const x: Item;", "x.k + 1"), Verdict::NoCheat);
    let root = r.canonical.to_string();
    assert!(root.starts_with("(lin 1 1 (dyn ") && !root.contains("dyn?"), "{root}");
    // A field the type does not name may hold anything, or nothing.
    let r = evaluate(&with("declare const x: Item;", "x.w")).unwrap();
    assert!(r.canonical.to_string().contains("dyn?"), "{}", r.canonical);
    // An interface names fields as a type literal does.
    let source = "interface Row { readonly n: number } declare const r: Row; r.n - r.n";
    assert_eq!(checked(source, Verdict::NoCheat).canonical.to_string(), "0");
}

#[test]
fn a_union_of_records_has_every_member_field() {
    initialize();
    let decls = "type Hist = { readonly kind: 'start' } | { readonly kind: 'edit'; readonly at: number; readonly prev: Hist }; declare const h: Hist;";
    // Every member names `kind`, so it is a string; only one names `at`, which may be missing.
    let r = checked(&format!("{decls} h.kind"), Verdict::NoCheat);
    let root = r.canonical.to_string();
    assert!(root.starts_with("(dyn ") && root.contains("shape:s"), "{root}");
    let r = evaluate(&format!("{decls} h.at")).unwrap();
    assert!(r.canonical.to_string().contains("dyn?"), "{}", r.canonical);
}

#[test]
fn a_spread_copies_the_declared_fields() {
    initialize();
    let r = checked(&with("declare const x: Item;", "({ ...x, k: x.k + 1 }).k - x.k"), Verdict::NoCheat);
    assert_eq!(r.canonical.to_string(), "1");
    let r = evaluate(&with("declare const x: Item;", "({ ...x })")).unwrap();
    assert!(!r.opaque && r.canonical.to_string().starts_with("(obj "), "{}", r.canonical);
    // A conditional between two records of one type has that type's fields.
    let r = checked(&with("declare const x: Item; declare const y: Item; declare const c: boolean;", "(c ? x : y).k - (c ? x : y).k"), Verdict::NoCheat);
    assert_eq!(r.canonical.to_string(), "0");
    // A spread of a value of unknown type stays unmodeled.
    assert!(evaluate("({ ...o }).x").unwrap().opaque);
}

#[test]
fn joint_runs_prove_order_free_steps_equal_and_report_opacity() {
    initialize();
    let decls = "declare const s: Item; declare const x: Item; declare const y: Item;";
    // A sum is the same in either order.
    let r = evaluate_joint(&[&with(decls, "s.k + x.k + y.k"), &with(decls, "s.k + y.k + x.k")]).unwrap();
    assert!(r.saturated && r.consistent && r.roots[0] == r.roots[1], "{:?}", r.canonical);
    assert_eq!(r.opaque, [false, false]);
    // Keeping the larger key is not: a tie keeps whichever came first.
    let step = "((a: Item, b: Item) => (b.k > a.k ? b : a))";
    let (xy, yx) = (format!("{step}({step}(s, x), y)"), format!("{step}({step}(s, y), x)"));
    let r = evaluate_joint(&[&with(decls, &xy), &with(decls, &yx)]).unwrap();
    assert_ne!(r.roots[0], r.roots[1], "{:?}", r.canonical);
    // A construct lowering does not model leaves the root an assumption, so a shared class
    // proves nothing about it.
    let r = evaluate_joint(&[&with(decls, "x.toString()"), &with(decls, "y.toString()")]).unwrap();
    assert_eq!(r.opaque, [true, true]);
}

#[test]
fn math_max_and_min_choose_by_order() {
    initialize();
    assert_eq!(checked("Math.max(2, 3)", Verdict::NoCheat).canonical.to_string(), "3");
    assert_eq!(checked("Math.min(2, 3)", Verdict::NoCheat).canonical.to_string(), "2");
    assert_eq!(checked("Math.max(undefined, 3)", Verdict::NoCheat).canonical.to_string(), "nan");
    // Over symbolic integers, a choice on their order.
    let r = checked(&with("declare const x: Item; declare const y: Item;", "Math.max(x.k, y.k)"), Verdict::NoCheat);
    assert!(r.canonical.to_string().starts_with("(if "), "{}", r.canonical);
    // Any other arity is not modeled.
    assert_eq!(evaluate("Math.max(1, 2, 3)").unwrap().verdict, Verdict::Undecided);
}
