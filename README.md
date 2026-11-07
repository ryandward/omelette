# omelette

An in-process Rust probe for absence laundering in JavaScript/TypeScript expressions: information flows by which a read that may be missing is quietly swallowed or conflated with an ordinary value. `names[i] ?? 'unknown'` writes a default; `names[i] !== 'off'` answers `true` when the element is missing; `names.slice(i, i + 1).every(p)` answers `true` for the empty list. Each has the form `maybe z f (xs !? k)`, and omelette proves it by finding a witness `maybe(family, z, x. f, read)` in an e-graph, where the family names the flow.

The runtime is [`egg`](https://github.com/egraphs-good/egg) with `oxc_parser` and `oxc_semantic`, all in-process. The 73 golden cases in [tests/cases.txt](tests/cases.txt) reach saturation with their expected verdicts. [docs/architecture.md](docs/architecture.md) describes the pipeline.

## Run and embed

`Cargo.toml` declares `rust-version = "1.97"`; development and the recorded benchmark use rustc 1.99.1.

```sh
cargo build --release
./target/release/omelette "names[i] ?? 'unknown'"
./target/release/omelette "names.slice(i, i + 1).every((n) => n !== 'off')"
./target/release/omelette 'users.map((_, i) => roles[i])' --all
./target/release/omelette --joint "names[i] !== 'off'" "names[i] === undefined || names[i] !== 'off'"
./scripts/check.sh
node scripts/differential.js FILE
cargo test --release
cargo run --release --example latency -- 500 --check
```

The command prints the verdict with its families, as in `verdict: CHEAT (sink)`. `--all` dumps every e-class; `--joint` saturates several expressions in one graph and prints each one's class, so a shared class proves them equal. `scripts/check.sh` runs the golden cases and fails on a verdict mismatch, a run that did not saturate, or an inconsistent graph. `scripts/differential.js` evaluates closed expressions (one per line) in both omelette and Node and fails where omelette claims a value Node does not produce.

```rust
use omelette::core::Family;
use omelette::engine::{evaluate, initialize, Verdict};

initialize(); // Once at startup: rules, parser bootstrap, egg's clock calibration.
let result = evaluate("names[i] ?? 'unknown'").expect("valid expression");
assert_eq!(result.verdict, Verdict::Cheat);
assert_eq!(result.families, [Family::Default]);
```

`evaluate` parses, resolves symbols, lowers, saturates a fresh graph, checks consistency, and extracts a canonical term; nothing is cached between expressions. It runs with a limit of 60 iterations, 10,000 e-nodes, and 50 ms; `evaluate_with_limits` takes a `Limits` value instead. They are cooperative bounds, not a real-time deadline. `parse_time` covers parsing, semantic analysis, and lowering. `TRACE=1` prints each iteration's graph size, search, apply, and rebuild time, and the rules applied. Syntax errors return `Err`.

## Verdicts

Checked in this order:

1. `UNDECIDED` if the run did not saturate, or the graph is inconsistent: two representations of one class proven different (two constants, or an empty integer interval).
2. `CHEAT` if a class reachable from the root holds a witness of a swallowing family over a read that is not proven present or missing, whose present branch mentions the element and is not a non-empty list against an empty replacement, and whose replacement `z` is certainly a value; or an `escape` of such a read (drift). The families are reported.
3. `UNDECIDED` if a witness leaves the answer to unknown inputs (its replacement may itself be `undefined`), or unsupported syntax or an unresolved call reaches the result.
4. `no cheat` otherwise.

## What counts as a cheat

| Family | The missing read becomes | Examples |
| --- | --- | --- |
| `default` | a value the program wrote | `xs[i] ?? 0`, `xs[i] === undefined ? 0 : xs[i]`, `xs.length ? xs[xs.length - 1] : 0`, `[...a, 0][0]` |
| `unit` | the unit of a fold's monoid | `xs.slice(i, i + 1).every(p)` (`true`), `.some(p)` (`false`), `.join('')` (`''`), `.filter(p).length` (`0`), `xs.slice(i, j).reduce((_, x) => x, 0)` |
| `container` | an empty collection | `groups.slice(i, i + 1).flat()`, `.flatMap((g) => g)` |
| `sink` | what an operator makes of `undefined` | `names[i] === 'on'`, `names[i] !== 'off'`, `widths[i] < 3`, `widths[i] + 1`, `names[i] + '!'`, `` `${names[i]}` ``, `!names[i]` |
| `drift` | a hole in a collection shaped like another | `users.map((_, i) => roles[i])`, `names.map((n, i) => names[i + 1])` |

These are not cheats: the read reaches the result unchanged (`names[i]`, `names[i] && names[i] !== 'off'`); it stays visible in a container (`names.slice(i, i + 1).map(f)`, `names[i] !== undefined ? [names[i]] : []`); its absence is observed rather than replaced (`names[i] === undefined`, `names.filter((_, k) => k === i).length === 0`, or a present branch that ignores the element); it throws when missing (`names[i].length`); the index is proven in range (`names.map((n, i) => names[i])`); or the operation speaks for a whole list (`names.every(p)`, `names.join(', ')`).

## Model

The verdicts concern this model, not general JavaScript safety.

- **Free variables** get a precondition from how the expression uses them: one used as an index, a slice or `at` bound, an operand of `-`, `*`, unary `-`, or an ordering comparison, or compared with a walker callback's own index parameter, is an integer; one used as a receiver or spread is a dense list whose elements are defined; one that is called is a function; any other may be anything, including `undefined`.
- **Numbers** are integers, exact up to 2^53 - 1 in magnitude; arithmetic beyond that, and non-integer literals, are not modeled. `+` is integer addition on integers, concatenation when an operand is a string, and otherwise an uninterpreted operation that is never `undefined`. Strings compare by UTF-16 code units; string ordering compares code units.
- **Calls** to known functions inline with JavaScript's arity: missing arguments are `undefined`, walkers pass (element, index, array) and `reduce` passes (accumulator, element, index, array). A call to an unknown function, or a walker over one, is unresolved.
- **Lists** of known length are evaluated element by element. On a symbolic list, `map`, `filter`, `every`, `some`, `join`, `flat`, and `reduce` stay walker terms, except where lowering knows more: a slice whose bounds differ by one, or a filter that keeps exactly `list[j]`, holds at most one element; a `reduce` whose callback ignores its accumulator yields its value on the last element. `flat` spreads an element of unknown type as if it may be a list.
- **Not modeled**, and `UNDECIDED` unless a witness elsewhere makes the expression a cheat: records and property reads other than `length`, `Map`, optional chaining, `null`, loose equality, `typeof`, mutation, loops, and statements other than `const`, `if`, blocks, and `return`.

## Latency

[benchmarks/latency.txt](benchmarks/latency.txt) records a release run with 500 samples per case on an Intel Core i7-8700K, and [benchmarks/environment.txt](benchmarks/environment.txt) records the toolchain and command. Each case gets five warmups; samples interleave all 73 cases, and each reparses the source and builds a new graph. Totals include dropping the graph.

| Measurement | Result |
| --- | ---: |
| Worst per-case parser p95 | 4.8 us |
| Worst per-case parser + semantic analysis + lowering p95 | 38.6 us |
| Worst per-case total p95 / p99 | 532.3 / 659.0 us |
| Largest total among 36,500 samples | 803.5 us |
| Worst total p95: original / string / every / some cases | 532.3 / 302.0 / 137.8 / 140.2 us |
| Worst total p95: unknown-callback / join and flat cases | 42.3 / 122.0 us |
| Two-element slice sum total p50 / p95 | 34.6 / 58.8 us |
| All-case graph sizes / iterations | 1-88 / 1-8 |
| One-time runtime initialization | 867.2 us |
| First evaluation after initialization | 118.2 us |

The worst case is `[0, ...widths.slice(i, i + 1)].filter((_, k) => k === widths.slice(i, i + 1).length)[0]`. These are measured samples on this host, not scheduling guarantees. `--check` requires every case's parser and parser-plus-lowering p95 below 50 us, total p95 below 1 ms, and fewer than 150 e-nodes; the tests assert correctness and graph bounds without wall-clock thresholds.
