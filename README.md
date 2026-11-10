# omelette

An in-process Rust probe for absence laundering in JavaScript/TypeScript expressions: information flows by which a read that may be missing is quietly swallowed or conflated with an ordinary value. `names[i] ?? 'unknown'` writes a default; `names[i] !== 'off'` answers `true` when the element is missing; `names.slice(i, i + 1).every((n) => n !== 'off')` answers `true` for the empty list. Each has the form `maybe z f (xs !? k)`: `z` where the read is missing, and `f` of the element where it is present. omelette proves it by finding a witness `maybe(family, z, x. f, read, has)` in an e-graph, where the family names the flow and `has` is the read's presence test.

It also reports observable mutation: whether the expression changes, in place, an array or object the caller holds. `xs.sort()` and `groups[i].push(x)` do. `[...xs].sort()` and `(() => { const a = []; a.push(x); return a; })()` mutate only an array they built themselves, which nobody else can see.

The runtime is [`egg`](https://github.com/egraphs-good/egg) with `oxc_parser` and `oxc_semantic`, all in-process. The 121 absence cases in [tests/cases.txt](tests/cases.txt) and the 66 mutation cases in [tests/mutations.txt](tests/mutations.txt) reach saturation with their expected verdicts. [tests/soundness.rs](tests/soundness.rs) and [tests/mutation.rs](tests/mutation.rs) hold the regressions from the soundness hunts. [docs/architecture.md](docs/architecture.md) describes the pipeline.

## Run and embed

`Cargo.toml` declares `rust-version = "1.97"`; development and the recorded benchmark use rustc 1.99.1.

```sh
cargo build --release
./target/release/omelette "names[i] ?? 'unknown'"
./target/release/omelette "names.slice(i, i + 1).every((n) => n !== 'off')"
./target/release/omelette 'users.map((_, i) => roles[i])' --all
./target/release/omelette --joint "names[i] !== 'off'" "names[i] === undefined || names[i] !== 'off'"
./target/release/omelette "declare const widths: number[]; widths[i] ?? 'none'"
./scripts/check.sh
node scripts/differential.js FILE
cargo test --release
cargo run --release --example latency -- 500 --check
```

The command prints the absence verdict with its families, as in `verdict: CHEAT (sink)`, and the mutation verdict with its operations, as in `mutation: MUTATION (sort)`. When lowering evaluated something it does not model, it also prints `opaque: yes`: both verdicts are then `UNDECIDED` unless a cheat or a mutation is found, and the root is the value under the model's assumptions, not a claim about JavaScript's result. `--all` dumps every e-class. `--joint` saturates several expressions in one graph and prints the graph's consistency and each expression's class. Each free variable gets one precondition from its uses across all the expressions. In a consistent graph, a shared class proves the expressions equal. `scripts/check.sh` runs both sets of golden cases and fails on a verdict mismatch, a run that did not saturate, or an inconsistent graph. `scripts/differential.js` evaluates closed expressions (one per line) in both omelette and Node. It fails on an inconsistent graph, a run that fails, or a value omelette claims that Node does not produce; an opaque run claims none. `scripts/erasure.js` checks verdicts the same way (see the image test).

```rust
use omelette::core::Family;
use omelette::engine::{evaluate, initialize, Mutation, Verdict};

initialize(); // Once at startup: rules, parser bootstrap, egg's clock calibration.
let result = evaluate("names[i] ?? 'unknown'").expect("valid expression");
assert_eq!(result.verdict, Verdict::Cheat);
assert_eq!(result.families, [Family::Default]);
assert_eq!(result.mutation, Mutation::None);
```

`evaluate` parses, resolves symbols, lowers, saturates a new graph, checks consistency, and extracts a canonical term. Only the rewrite rules are shared between calls; egg's global symbol table also keeps every variable name and string it interns for the life of the process. It runs with a limit of 60 iterations, 10,000 e-nodes, and 50 ms; `evaluate_with_limits` takes a `Limits` value instead. These are cooperative bounds, not a real-time deadline. `parse_time` covers parsing, semantic analysis, and lowering. Setting `TRACE` to any value prints each iteration's graph size, search, apply, and rebuild time, and the rules applied. A syntax error, or source that is not a single expression, returns `Err`.

## Verdicts

Checked in this order:

1. `UNDECIDED` if the run did not saturate, or the graph is inconsistent: a class proven to hold two different constants, or an empty integer interval.
2. `CHEAT` if a witness or an escape shows a swallowed read. The families are reported. A witness counts when the root has no representative that avoids its class, its read is not proven in or out of range, and all of these hold:
   - its family swallows;
   - some witness of that class over that read has a replacement that is certainly a value, with no throw in it;
   - every representative of its present branch mentions the element, and some representative is free of unknown functions, unknown values, and unsupported syntax;
   - its replacement is not apart from its present branch (see the image test below);
   - the element it reads cannot itself be `undefined`.

   An escape of such a read whose replacement is still `undefined` is drift.
3. `UNDECIDED` if the answer depends on unknown inputs, or on something lowering does not model:
   - a witness's family is undecided, its replacement may itself be `undefined` or throw, its present branch holds an unknown, or the element it reads may itself be `undefined`;
   - a witness passes the missing read on as `undefined`, but its present branch may produce `undefined` too: `xs[i] === undefined ? undefined : xs[i].length`, where a present `0` has no length;
   - a witness's present branch avoids the element only by reading the same free list another way, as in `xs[i] === undefined ? 0 : xs.slice(i, i + 1)[0]`, which may read that element;
   - lowering evaluated unsupported syntax, an unresolved call, a walker over an unknown callback, or a spread of a value of unknown type, anywhere in the expression;
   - such a construct reaches the result.
4. `no cheat` otherwise.

## What counts as a cheat

| Family | The missing read becomes | Examples |
| --- | --- | --- |
| `default` | a value the program wrote | `xs[i] ?? 0`, `xs[i] === undefined ? 0 : xs[i]`, `xs.length ? xs[xs.length - 1] : 0`, `[...a, 0][0]` |
| `unit` | the unit of a fold's monoid, including a walker whose callback holds at one index only: `names.some((n, k) => k === i && n === 'admin')` is `names.slice(i, i + 1).some(...)` | `xs.slice(i, i + 1).every((x) => x > 0)` (`true`), `.some((x) => x > 0)` (`false`), `.join('')` (`''`), `.filter((x) => x > 0).length` (`0`), `xs.slice(i, j).reduce((_, x) => x, 0)` |
| `container` | an empty collection, which a filter that drops a present element also makes: `names.slice(i, i + 1).filter((n) => n !== '')` | `groups.slice(i, i + 1).flat()`, `.flatMap((g) => g)` |
| `sink` | what an operator or a conversion makes of `undefined` | `names[i] === 'on'`, `names[i] !== 'off'`, `widths[i] < 3`, `widths[i] + 1`, `names[i] + '!'`, `` `${names[i]}` ``, `!names[i]`, `Number(widths[i])`, `+widths[i]`, `parseInt(names[i])`, `String(names[i])`, `Boolean(names[i])`, `JSON.stringify([names[i]])` |
| `drift` | a hole in a collection shaped like another | `users.map((_, i) => roles[i])`, `names.map((n, i) => names[i + 1])` |

These are not cheats:

- the read reaches the result unchanged: `names[i]`, `names[i] && names[i] !== 'off'`;
- it stays visible in a container: `names.slice(i, i + 1).map((n) => n.length)`, `names[i] !== undefined ? [names[i]] : []`;
- its absence is observed rather than replaced: `names[i] === undefined`, `names.filter((_, k) => k === i).length === 0`, `names.some((_, k) => k === i)`, or a present branch that ignores the element;
- its replacement is a value the present branch never produces: `` names[i] === undefined ? -1 : `${names[i]}`.length ``, `names[i] === undefined ? 'none' : names[i] > 0`;
- it throws when missing: `names[i].length`;
- the index is proven in range: `names.map((n, i) => names[i])`, `xs.map((x) => xs[0] ?? 0)`;
- the operation speaks for a whole list: `names.every((n) => n !== 'off')`, `names.join(', ')`, `names.map(Number)`, `names.filter(Boolean)`.

The spellings of one computation agree. Dropping the missing reads, `users.flatMap((_, k) => roles[k] === undefined ? [] : [roles[k]])`, is honest: each slot gives `[]` where its read is missing and `[role]` where it is present, so the absence shows in the length. So is the fold `users.reduce((acc, _, k) => roles[k] === undefined ? acc : [...acc, roles[k]], [])`, whose accumulator is never the same length as itself with an element appended, and so is `forEach` pushing onto a local array, which lowers to the same fold. Keeping each read, as `users.map((_, k) => roles[k])`, `users.reduce((acc, _, k) => [...acc, roles[k]], [])`, or a `forEach` that pushes `roles[k]`, leaves holes and is `drift`. One spelling still disagrees: `users.map((_, k) => roles[k]).filter((r) => r !== undefined)` is reported as `drift` for the holes in its intermediate list, though the filter removes them before the result.

A `catch` is a fallback too. In `(() => { try { return names[i].length; } catch { return 0; } })()`, the missing read throws and the handler writes `0`, which a present `''` also gives, so it is a `default` cheat. With `declare const names: string[];` and `return -1`, it is honest. A `try` block is modeled when it ends in `return`, so it never falls through; a value that may throw for a reason lowering cannot name, such as an unknown call, leaves the verdict undecided, and `finally` is not modeled.

`JSON.stringify(names[i])` passes the missing read on as `undefined`, but a present function writes `undefined` too, so it is undecided until the elements' types rule functions out.

### The image test

A fallback `z` erases the missing read exactly when `z` is also the result of some present element: `c(undefined)` lies in the image of `c` over present elements. Detection proves the opposite, that `z` is apart from the present branch, from facts the analysis keeps for every class. The facts are the JavaScript types a value can have (`undefined`, boolean, number, string, list, object, function), integer bounds, constants, the element types of lists, and the constant prefixes and suffixes of strings. A replacement is apart from a branch when it has a type the branch never has, is another constant, lies outside the integers or the bounds the branch keeps to, misses a prefix or suffix the branch's text always has, or is a list whose head or tail differs from every one the branch builds. A conditional in either is compared arm by arm. A condition that shares no variable with the read stays fixed while the read varies. Where the replacement and the branch both test such a condition, each side is compared under it, and a world where the two are one term never evaluates the read, so it erases nothing. A condition on the read's own variables may be its presence test, which differs between the two sides, so it never splits them.

An input list's elements are never `undefined`, but nothing else is known about them: an element may be any value, including an object with any `length`. So `names[i] === undefined ? [] : names[i].length` is a cheat, because `{ length: [] }` is an element too.

### Definitions

A source may also define helpers before its expression, as `const name = value;` or `function name() {}`, which the expression and each other may call: `const listed = (v) => v === undefined ? [] : [v]; listed(names[i]).reduce((_, x) => x, 'COUNT')` is a `default` cheat, the same fold as `names.slice(i, i + 1).reduce(...)`. Functions are hoisted, a `const` is defined in order, and one whose value throws makes the program throw. Only `declare const`, named `const` definitions, and named functions may precede the expression.

### Declared types

Leading `declare const` statements give free variables TypeScript types, which narrow what their values and elements can be. With `declare const names: string[];`, `names[i] === undefined ? [] : names[i].length` is honest, `names[i] ?? 0` is honest (no string is `0`), and `names[i] ?? ''` is still a cheat. With `declare const users: object[];`, `Boolean(users[i])` is honest: an object is always truthy, so `false` marks the missing read. With `declare const widths: number[];`, `JSON.stringify(widths[i])` is honest, since a number always writes text.

TypeScript checks structure, and so does the model. `object` admits arrays and functions. `Object`, `{}`, and `Record` admit primitives too. A type literal rules primitives out only when it requires a member no string, number, or boolean has, so `{ id: number }[]` elements are always truthy, but `{ length: number }[]` elements may be strings, `''` among them. A type omelette does not resolve, such as an interface or an alias, admits anything. An element type that admits `undefined`, as in `(string | undefined)[]`, makes a present element indistinguishable from a missing one, so a branch that varies there is undecided. `null`, `bigint`, and `symbol` are not modeled, and a declaration that admits them is an error, as is one that redeclares a global omelette models, such as `String`.

`scripts/erasure.js` checks verdicts against this definition. It takes expressions that mention `xs` only at `i` (as `xs[i]`, `xs.at(i)`, or `xs.slice(i, i + 1)`), optionally with a context `c`, `j` and a declared element type. It evaluates each on a missing read and on a pool of present elements in Node, and fails on a `no cheat` where some element gives the missing read's result. A present `undefined` collides with every missing read, whatever the program, so it does not count.

Where an unknown decides the flow, the verdict is `UNDECIDED`. `names[i] === x` only tests presence when `x` is `undefined`. `xs.slice(i, i + 1).some(p)` does too when `p` always returns `true`, and it is constant when `p` always returns `false`.

## Observable mutation

Checked in this order:

1. `UNDECIDED` if the run did not saturate, or the graph is inconsistent.
2. `MUTATION` if a mutation that can run reaches an array or object someone outside the expression holds. The operations are reported.
3. `UNDECIDED` if a mutation that can run reaches an object whose holder is unknown, or lowering evaluated anything it does not model, which may mutate.
4. `none` otherwise.

| Who holds the mutated array | Examples | Verdict |
| --- | --- | --- |
| the caller | `xs.sort()`, `xs.push(1)`, `xs[i] = 0`, `xs.length = 0`, `o.name = 'x'`, `delete xs[i]`, `xs[i]++` | `MUTATION` |
| the caller, through an element or an alias | `groups[i].push(1)`, `groups.map((g) => g.sort())`, `((a) => a.reverse())(xs)`, `xs.map((x, i, a) => a.pop())` | `MUTATION` |
| the caller, after an array the expression built escapes into one of theirs | `(() => { const a = []; xs.push(a); a.push(1); return 0; })()` | `MUTATION` |
| the expression alone | `[...xs].sort()`, `xs.slice().reverse()`, `xs.map((x) => x * 2).sort()`, `(() => { const a = []; a.push(1); return a; })()`, `(() => { const rows = [[], []]; rows[0].push(1); return rows; })()` | `none` |
| unknown | `f(xs)`, `xs.map(f)`, `xs.forEach((x) => x)`, a `reduce` that mutates its accumulator | `UNDECIDED` |

A mutation counts only where it can run. These mutate nothing:
- `xs.length >= 0 ? 0 : ys.push(1)`;
- `xs.filter(() => false).map((x) => ys.push(x))`;
- `[0, 1].every((x) => x > 0 && xs.push(1))`;
- `[1].sort((a, b) => (ys.push(1), 0))`, since a comparator runs only on two or more elements;
- `(xs.length > 0 ? 0 : xs[0].push(1))`, which throws before it can push.

`xs[i] === undefined ? ys.push(1) : 0` mutates `ys` where the read is missing. A local array escapes only where the code that stores it runs.

Every array has an identity once it can be held: bound to a name, put in another array, read from a list lowering recomputes, or made the receiver of a list method. Its aliases share its contents, so a mutation through one is seen through all of them, and values after a mutation are computed from the updated contents: `(xs.length = 0, xs[0] ?? 5)` is `5`. Some values become unknown, and leave the verdicts `UNDECIDED`, rather than risk being stale: an array stored into a symbolic list, an array whose contents a term already holds once it changes, an array that contains itself, and anything an object of unknown holder may be. The model adds two preconditions: distinct free variables are distinct objects, and a free list's elements are distinct from every free variable.

## Model

The verdicts concern this model, not general JavaScript safety.

- **Free variables** get a precondition from how the expression uses them, looking through parentheses and type assertions.
  - A variable used as an index, a `slice` or `at` bound, an operand of `-`, `*`, unary `-`, or an ordering comparison, or compared with a walker callback's own index parameter, is an integer.
  - One used as a receiver or spread is a dense list whose elements are defined.
  - One that is called is a function.
  - Any other may be anything, including `undefined`.
- **Numbers** are integers. Symbolic integer arithmetic is assumed exact, so every intermediate value stays within 2^53 - 1 in magnitude. A value or term whose constant or coefficient lies beyond that is not folded, and non-integer literals are not modeled.
  - `+` concatenates when an operand is a string or a list, and otherwise adds integers and booleans.
  - An `undefined` or `NaN` operand makes arithmetic `NaN`.
  - Any other `+` is an uninterpreted operation that is never `undefined`.
- **Strings** compare by UTF-16 code units, and string ordering compares code units. Spread and array destructuring iterate code points.
- **Lists** compare by identity. A list built with `undefined` elements, such as `[undefined, ...ys]` or a map whose callback may return `undefined`, does not inherit the precondition's defined elements. A witness over such an element is `UNDECIDED`: a branch that varies only at the `undefined` element observes presence, and detection cannot separate that from a cheat. On a symbolic list, `map`, `filter`, `every`, `some`, `join`, `flat`, and `reduce` stay walker terms, except where lowering knows more:
  - a slice whose bounds differ by one, `slice(-1)`, or a filter that keeps exactly `list[j]` holds at most one element;
  - a `reduce` whose callback ignores its accumulator yields its value on the last element;
  - inside a walker's callback, reads at the walker's index of lists at least as long as the walked one, and at their first and last elements, are present.

  `flat` spreads an element of unknown type as if it may be a list.
- **Calls** to known functions inline with JavaScript's arity. Missing arguments are `undefined`, walkers pass (element, index, array), and `reduce` passes (accumulator, element, index, array). Calling a value that is not a function, passing one as a callback, or reading a property of `undefined` throws. A call to an unknown function, or a walker over one, is unresolved, and a fold whose seed may be missing is undecided.
- **Effects**: a throw is an effect, not a value. An array element, call operand, `const` initializer, or operator operand that throws makes the expression throw in that world, so a read that throws when missing is never swallowed. A walker's callback that throws on some element is the exception: the walker term stands for the list it would build.
- **Not modeled**, and `UNDECIDED` unless a witness elsewhere makes the expression a cheat:
  - records and property reads other than `length`, `Map`, optional chaining, and `null`;
  - loose equality, `typeof`, `in`, `instanceof`, `/`, `%`, `**`, bitwise operators, and unary `+`;
  - loops, `throw`, `let` and `var`, assignment to a variable, and statements other than `const`, `if`, blocks, expressions, and `return`;
  - array methods other than those named here, such as `forEach`, `includes`, and `indexOf`;
  - named, async, and generator functions; rest parameters and rest elements; and `arguments`;
  - `flat` beyond depth one, `at` with an index of unknown sign, and `slice` of a literal list with symbolic bounds.

## Latency

[benchmarks/latency.txt](benchmarks/latency.txt) records each case's parser, parser-plus-lowering, and total quantiles from a release run with 500 samples per case. [benchmarks/environment.txt](benchmarks/environment.txt) records the host (an Intel Core i7-8700K), the toolchain, the protocol, and the command. Each case gets five warmups; samples interleave all 137 cases, the 73 absence cases and then the 64 mutation cases, and each reparses the source and builds a new graph. Totals include dropping the graph.

| Measurement | Result |
| --- | ---: |
| Worst per-case parser p95 | 4.9 us |
| Worst per-case parser + semantic analysis + lowering p95 | 32.6 us |
| Worst per-case total p95 / p99 | 368.3 / 561.1 us |
| Largest total among 68,500 samples | 676.9 us |
| Worst total p95: original / string / every / some cases | 368.3 / 274.4 / 135.7 / 144.6 us |
| Worst total p95: unknown-callback / join and flat cases | 46.5 / 117.2 us |
| Worst total p95: mutation cases | 255.0 us |
| Two-element slice sum total p50 / p95 | 43.6 / 49.0 us |
| All-case graph sizes / iterations | 1-76 / 1-8 |
| One-time runtime initialization | 830.6 us |
| First evaluation after initialization | 187.9 us |

The worst case is `[0, ...widths.slice(i, i + 1)].filter((_, k) => k === widths.slice(i, i + 1).length)[0]`. These are measured samples on this host, not scheduling guarantees. `--check` requires every case's parser and parser-plus-lowering p95 below 50 us, total p95 below 1 ms, and fewer than 150 e-nodes; the tests assert correctness and graph bounds without wall-clock thresholds.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT) at your option. Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this crate by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
