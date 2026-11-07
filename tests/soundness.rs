//! Regressions from the soundness hunt on the previous engine, by root cause.
mod common;
use common::{checked, cheat, value};
use omelette::core::Family;
use omelette::engine::Verdict;

#[test]
fn statements_after_a_branch_that_does_not_return_still_run() {
    value("(() => { if (true) {} return 5; })()", "5");
    cheat("(() => { if (names[i] !== undefined) {} else { return 'x'; } return names[i]; })()", &[Family::Default]);
}

#[test]
fn a_projection_through_filter_is_a_list_of_at_most_one_read() {
    cheat("names.filter((_, k) => k === i).every((n) => n !== 'off')", &[Family::Unit]);
    cheat("names.filter((_, k) => k === i).join('')", &[Family::Unit]);
    cheat("names.slice(-1).every((n) => n !== 'off')", &[Family::Unit]);
}

#[test]
fn joining_one_possibly_missing_read_is_a_cheat() {
    cheat("[names[i]].join('')", &[Family::Unit]);
}

#[test]
fn logical_operators_return_their_operands() {
    value("[1, 2].length || 7", "2");
    value("0 && false", "0");
    checked("names[i] && names[i] !== 'off'", Verdict::NoCheat);
}

#[test]
fn list_operations_apply_only_to_lists() {
    value("[].concat(5) === 5", "false");
    value("[...'ab'] === 'ab'", "false");
    checked("'ab'[0] ?? 'z'", Verdict::NoCheat);
}

#[test]
fn a_witness_in_an_unused_branch_does_not_count() {
    for source in ["true ? 5 : names[i] ?? 'x'", "[].length ? names[i] ?? 'x' : 5", "[names[i] ?? 'x'].length", "((y) => 5)(names[i] ?? 'x')"] {
        checked(source, Verdict::NoCheat);
    }
}

#[test]
fn present_but_undefined_elements_are_not_absent() {
    value("[...[1].map((x) => undefined), 0][0]", "undefined");
    value("((ys) => ys.every((y, k) => ys[k] !== undefined))([1].map((x) => undefined))", "false");
}

#[test]
fn an_index_that_is_not_an_integer_selects_nothing() {
    value("[1, 2].find((_, idx) => idx === '0')", "undefined");
}

#[test]
fn integers_beyond_exact_range_are_not_folded() {
    let r = checked("9007199254740991 + 1 === 9007199254740991 + 2", Verdict::NoCheat);
    assert_ne!(r.canonical.to_string(), "false");
}
