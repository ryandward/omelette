# omelette

An in-process Rust probe for absence laundering in JavaScript/TypeScript expressions. For example, `widths.slice(i, i + 1).reduce((_, x) => x, 0)` replaces a potentially absent read with a written default. omelette proves this by finding a `Maybe(default, IndexQ(array, index))` representation.

The runtime uses **`egg`**, with **`oxc_parser` / `oxc_allocator`** for native parsing. There are no Node.js, TypeScript compiler, or parser subprocesses. All 29 golden cases pass and reach saturation, including both index-equality `find` predicates. `widths.length ?? 0` resolves to `no cheat`.

## Run and embed

Requires Rust 1.97 or newer.

```sh
cargo build --release
./target/release/omelette 'widths.find((_, idx) => idx === i) ?? 0'
./target/release/omelette 'widths.length ?? 0' --all
./target/release/omelette --joint 'widths.find((_, idx) => idx === i)' 'widths[i]'
./scripts/check.sh
cargo test --release
cargo run --release --example latency -- 500 --check
```

Use the library inside the harness loop:

```rust
use omelette::engine::{evaluate, initialize, Verdict};

initialize(); // Once at harness startup: rules, parser bootstrap, egg's clock calibration.
let result = evaluate("widths[i] ?? 0").expect("valid expression");
assert_eq!(result.verdict, Verdict::Cheat);
assert!(result.saturated && result.consistent);
```

`evaluate` includes parsing, lowering, graph construction, saturation, consistency checking, and extraction. It creates a fresh graph for every input; expression results are not cached. The shared rules are initialized once. `parse_time` includes both parsing and lowering; `total_time` ends before disposal of the returned graph. The benchmark additionally includes that disposal. `TRACE=1` prints applications per iteration.

`evaluate_with_limits` exposes iteration, node, and saturation-time limits. Defaults are 60 iterations, 10,000 nodes, and 50 ms. Limits are cooperative engine bounds, not a hard real-time deadline; a limit or inconsistent graph returns `UNDECIDED`. Syntax errors return `Err`.

## Why egg

The basis needs directed algebraic rules plus small interval and free-variable analyses. It does not require a general Datalog runtime. `egglog` made those analyses concise, but the supplied baseline was 10–53 ms of saturation alone. The native implementation removes the subprocess frontend and the per-expression Datalog setup and joins. It meets the sub-millisecond steady-state target for this basis on the measured host; this is not a worst-case guarantee for arbitrary JavaScript or operating-system scheduling.

- [frontend.rs](src/frontend.rs) lowers the Oxc AST directly into terms. Addition, subtraction, negation, and constant multiplication become canonical affine forms **before entering egg**. Terms use integer coefficients instead of expanding constants into repeated units. Nonlinear multiplication stays opaque arithmetic.
- [rules.rs](src/rules.rs) contains the directed `egg::rewrite!` rules. Explicit mirror rules handle `===`; there is no general equality commutation, association, or inverse arithmetic expansion. The former [rules.egg](src/rules.egg) remains as a historical specification, outside the runtime.
- [engine.rs](src/engine.rs) tracks interval bounds and free variables. Globally fresh frontend binders and free-variable guards prevent capture during beta reduction. Arithmetic introduced by semantic rewrites uses the same affine representation, with checked integer operations and coefficient merging after e-class unions.
- Index predicates lower to `Select`, a list containing at most the selected element. Projection then becomes an indexed read without distributing conditionals through the entire list. Short-list bounds are consumed directly by folds and reads. Structural rules skip cyclic identity representatives such as `Append(xs, Nil)` after it merges with `xs`.
- The relational M1 lemma uses a hash-cons lookup for the matching partial read. Its applier reports only changed unions, so repeated matches do not falsely prevent saturation.

The two-element slice sum is deliberately left as a fold: its length bound is `[0, 2]`, so the singleton-fold lemma cannot fire. Its regression test requires `no cheat`, saturation, consistency, and fewer than 150 e-nodes.

## Reproducible latency measurements

[benchmarks/latency.txt](benchmarks/latency.txt) records a release-mode run with 500 samples per case on an Intel Core i7-8700K. [benchmarks/environment.txt](benchmarks/environment.txt) records the toolchain and command. Each case gets five warmups; samples interleave all 29 inputs. Each timed evaluation reparses the source and constructs a new graph. The benchmark reports runtime startup and the first evaluation separately, then p50/p95/p99/max latency for the steady-state loop.

Recorded results (microseconds; total includes graph disposal):

| Measurement | Result |
| --- | ---: |
| Worst per-case parser p95 | 4.5 µs |
| Worst per-case parser + lowering p95 | 26.5 µs |
| Worst per-case total p95 / p99 | 536.9 / 768.9 µs |
| Largest total among 14,500 samples | 987.5 µs |
| Two-element sum total p50 / p95 | 139.1 / 191.0 µs |
| Two-element sum graph / iterations | 28 / 5 |
| All-case graph sizes / iterations | 6–74 / 1–9 |
| One-time runtime initialization | 1,410.1 µs |
| First evaluation after initialization | 371.0 µs |

These are measured samples on this host, not scheduling guarantees.

The `--check` option requires every case's parser and parser-plus-lowering p95 to be below 50 µs, total p95 below 1 ms, and graph size below 150 e-nodes. Ordinary tests assert correctness and graph bounds without wall-clock thresholds. `scripts/check.sh` also rejects non-saturated runs, including cases whose expected verdict is `UNDECIDED`.

## Verdicts and model boundaries

- `CHEAT`: a reachable class contains `Maybe(z, m)`, where `m` is an undetermined `IndexQ` and `z` is a written value.
- `no cheat`: saturation completed, the extracted expression has no unsupported syntax, and no such pattern was found.
- `UNDECIDED`: unsupported syntax or unresolved callees remain, the engine reached a limit, or consistency checks failed.

These verdicts concern the existing algebraic model, not general JavaScript safety. Arithmetic models integers, not IEEE-754 behavior (`NaN`, infinities, rounding, and signed zero). Lists are dense and in-bounds reads are assumed defined; sparse arrays and stored `undefined` values are outside the model. Records, mutation, side effects, and general control flow are not modeled. Blocks support straight-line `const` bindings and returning branches; logical operators retain the basis's boolean interpretation. Callbacks model the element and index, not the array argument. Unknown callees remain unresolved. Symbolic slice bounds remain semantic `Rel` terms until concrete bounds justify expansion.
