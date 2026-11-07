mod common;
use common::{checked, cheat};
use omelette::core::Family;
use omelette::engine::Verdict;

#[test]
fn each_family_has_its_canonical_witness() {
    for (source, family, witness) in [
        ("names[i] ?? 'x'", Family::Default, "(maybe default utf16:0078 (lam elem:@1 elem:@1) (read list:names int:i))"),
        ("names[i] !== 'off'", Family::Sink, "(maybe sink true (lam elem:@1 (not (eq elem:@1 utf16:006f00660066))) (read list:names int:i))"),
        ("names[i] === 'on'", Family::Sink, "(maybe sink false (lam elem:@1 (eq elem:@1 utf16:006f006e)) (read list:names int:i))"),
        (
            "names.slice(i, i + 1).join('')",
            Family::Unit,
            "(maybe unit utf16: (lam elem:@1 (text elem:@1)) (read (slice list:names int:i (lin 1 1 int:i)) 0))",
        ),
        ("users.map((_, i) => roles[i])", Family::Drift, "(map (lam elem:@1 index:@2 (escape (read list:roles index:@2))) list:users)"),
    ] {
        let r = cheat(source, &[family]);
        assert_eq!(r.canonical.to_string(), witness, "{source}");
    }
}

#[test]
fn every_family_is_reported() {
    for (source, family) in [
        ("xs.length ? xs[xs.length - 1] : 0", Family::Default),
        ("[...widths.slice(i, i + 1), 0][0]", Family::Default),
        ("[0, ...xs][xs.length]", Family::Default),
        ("names.slice(i, i + 1).every((n) => n !== 'off')", Family::Unit),
        ("names.slice(i, i + 1).some((n) => n === 'on')", Family::Unit),
        ("names.slice(i, i + 1).filter((n) => n === 'on').length", Family::Unit),
        ("widths.slice(i, j).reduce((_, x) => x, 0)", Family::Unit),
        ("groups.slice(i, i + 1).flat()", Family::Container),
        ("groups.slice(i, i + 1).flatMap((g) => g)", Family::Container),
        ("widths[i] < 3", Family::Sink),
        ("widths[i] + 1", Family::Sink),
        ("names[i] + '!'", Family::Sink),
        ("`${names[i]}`", Family::Sink),
        ("!names[i]", Family::Sink),
        ("names.map((n, i) => names[i + 1])", Family::Drift),
    ] {
        cheat(source, &[family]);
    }
}

#[test]
fn observing_or_keeping_absence_is_not_a_cheat() {
    for source in [
        "names[i]",
        "names[i] === undefined",
        "names[i] !== undefined ? true : false",
        "names[i] !== undefined ? y : 5",
        "names[i] !== undefined ? [names[i]] : []",
        "names[i] && names[i] !== 'off'",
        "names.slice(i, i + 1).map((n) => n !== 'off')",
        "names.slice(i, i + 1).flatMap((n) => [n])",
        "names.slice(i, i + 1).length",
        "names.filter((_, k) => k === i).length === 0",
        "names.every((n) => n !== 'off')",
        "names.join(', ')",
        "names.map((n, i) => names[i] !== 'off')",
        "names.map((n) => 5)[i] ?? 0",
        "names[i].length",
    ] {
        checked(source, Verdict::NoCheat);
    }
}

#[test]
fn a_replacement_that_may_be_undefined_is_undecided() {
    for source in ["names[i] ?? y", "widths[i] === j", "xs.map(f)", "somefn() ?? 0"] {
        checked(source, Verdict::Undecided);
    }
}
