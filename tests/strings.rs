mod common;
use common::checked;
use omelette::engine::Verdict;

#[test]
fn genomehub_text_and_empty_defaults_use_the_same_rules() {
    for default in ["MODE", "measures", "none", ""] {
        for source in [
            format!("names[i] ?? '{default}'"),
            format!("names[i] === undefined ? '{default}' : names[i]"),
            format!("names.reduce((_, n) => n, '{default}')"),
            format!("names.slice(i, i + 1).reduce((_, n) => n, '{default}')"),
            format!("[...names.slice(i, i + 1), '{default}'][0]"),
        ] {
            let r = checked(&source, Verdict::Cheat);
            assert!(
                r.graph[r.root]
                    .nodes
                    .iter()
                    .any(|n| n.op.as_str() == "Maybe")
            );
        }
    }
}

#[test]
fn strict_equality_uses_decoded_string_values_without_coercion() {
    for (source, expected) in [
        ("'a' === 'a'", true),
        ("'a' === 'b'", false),
        ("'a' === undefined", false),
        ("undefined === 'a'", false),
        ("'1' === 1", false),
        ("1 === '1'", false),
        ("'true' === true", false),
        ("false === ''", false),
        ("'' === ''", true),
        (r"'\x61' === 'a'", true),
        (r"'\u0061' === 'a'", true),
        (r"'\ud83d\ude00' === '😀'", true),
        (r"'\ud800' === '\ud800'", true),
        (r"'\ud800' === '\ud801'", false),
        (r"'\ud800' === '�'", false),
        (r"'\n' === '\\n'", false),
        ("'a b' === 'a b'", true),
    ] {
        let r = checked(source, Verdict::NoCheat);
        assert_eq!(
            r.canonical.to_string(),
            format!("(B {expected})"),
            "{source}"
        );
    }
}

#[test]
fn concatenation_stays_ordered_and_out_of_affine_arithmetic() {
    let r = checked("names.map((n) => n + '!')", Verdict::NoCheat);
    assert!(
        r.canonical
            .as_ref()
            .iter()
            .any(|n| n.op.as_str() == "Concat")
    );
    assert!(
        !r.canonical
            .as_ref()
            .iter()
            .any(|n| n.op.as_str().starts_with("Lin:"))
    );
    for (source, expected) in [
        ("'a' + 'b' === 'ab'", true),
        ("'a' + 'b' === 'b' + 'a'", false),
        ("'a' + '' === 'a'", true),
        ("'a' + 'b' === undefined", false),
        ("((n) => n + '!')('a') === 'a!'", true),
    ] {
        let r = checked(source, Verdict::NoCheat);
        assert_eq!(
            r.canonical.to_string(),
            format!("(B {expected})"),
            "{source}"
        );
    }
    // Neither direction may canonicalize string concatenation as a commutative sum.
    let r = omelette::engine::evaluate_joint(&["n + '!'", "'!' + n"]).unwrap();
    assert!(r.saturated);
    assert_ne!(r.roots[0], r.roots[1]);
}

#[test]
fn known_string_values_are_not_absent_reads() {
    for source in [
        "'MODE' ?? 'unknown'",
        "'' ?? 'unknown'",
        "('a' + 'b') ?? 'unknown'",
        "['a'][0] ?? 'unknown'",
        "['a'].reduce((_, n) => n, 'unknown')",
        "[].reduce((_, n) => n, 'unknown')",
        "names.filter((n) => n !== 'off')",
        "names[i] !== undefined ? names[i] : undefined",
    ] {
        checked(source, Verdict::NoCheat);
    }
    let r = checked("'' ?? 'unknown'", Verdict::NoCheat);
    assert_eq!(r.canonical.to_string(), "(Str utf16:)");
}

#[test]
fn string_constants_keep_their_value_and_type_in_joint_graphs() {
    let r = omelette::engine::evaluate_joint(&["'a'", "'b'", "0", "undefined", "true", "'a' + ''"])
        .unwrap();
    assert!(r.saturated);
    for i in 0..5 {
        for j in i + 1..5 {
            assert_ne!(r.roots[i], r.roots[j], "roots {i} and {j} merged");
        }
    }
    assert_eq!(r.roots[0], r.roots[5]);
}

#[test]
fn conflicting_string_constants_are_detected_by_analysis() {
    use omelette::engine::Graph;
    for other in ["(Str utf16:0062)", "(Num 0)", "(B true)"] {
        let mut graph = Graph::default();
        let a = graph.add_expr(&"(Str utf16:0061)".parse().unwrap());
        let b = graph.add_expr(&other.parse().unwrap());
        graph.union(a, b);
        graph.rebuild();
        assert!(
            graph[a].data.clash,
            "merging a string with {other} must clash"
        );
    }
}

#[test]
fn other_existing_default_shapes_accept_strings() {
    for source in [
        "names[i] !== undefined ? names[i] : 'unknown'",
        "(([n = 'unknown']) => n)(names.slice(i, i + 1))",
        "['unknown', ...names][names.length]",
        "names.at(-1) ?? 'unknown'",
        "['unknown', ...names].reduce((_, n) => n)",
        "names.slice(i, j).reduce((_, n) => n, 'unknown')",
        "((f) => f() ?? 'unknown')(() => names[i])",
        "names.find((_, idx) => idx === i) ?? 'unknown'",
        "names.find((_, idx) => i === idx) ?? 'unknown'",
        "['unknown', ...names.slice(i, i + 1)].filter((_, k) => k === names.slice(i, i + 1).length)[0]",
    ] {
        checked(source, Verdict::Cheat);
    }
    checked("names.length ?? 'none'", Verdict::NoCheat);
}
