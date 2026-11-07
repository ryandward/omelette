# omelette

This is an equality-saturation probe for absence laundering in TypeScript. Laundering is a total-typed expression that quietly turns a missing value into a default, such as `widths.slice(i, i + 1).reduce((_, x) => x, 0)`. The type checker sees `number` and has nothing to say. omelette tries to prove that the reader decomposes into `maybe(default, index?(xs, k))`, an absent read eliminated with a value the program wrote.

The pipeline has two parts:

- `frontend/dump.ts` lowers one TS expression to an S-expression. It works on syntax only and gives no node a meaning.
- `src/rules.egg` and `src/bin/omelette.rs` are the [egglog](https://github.com/egraphs-good/egglog) engine. The rules give `slice`, `reduce`, `filter`, `find`, `??`, destructuring defaults and the rest their ECMAScript meaning. The driver declares the constructors, generates the free-variable, depth and let-substitution rules that are the same for every constructor, runs to saturation, and reads the e-graph back for the query.

Intervals (`lo`/`hi`, merged by max/min) and free variables (merged by set intersection) are functions with lattice merges. Integer arithmetic gets one affine normal form per class, `Lin(form)`, where the form is a multiset of atoms. Equal sums build the same `Lin` node and hash-consing merges them, so there are no commutativity or associativity rewrites.

## Run

```
cargo build --release
./target/release/omelette                                # the default cases
./target/release/omelette '<expr>' ['<expr>' ...]        # one run per expression
./target/release/omelette '<expr>' --all                 # print every e-class reachable from the root
./target/release/omelette --joint '<expr>' '<expr>' ...  # one e-graph; shows which roots share a class
./scripts/check.sh                                       # every case in tests/cases.txt against its expected verdict
```

The binary needs `node` on your PATH. The dumper loads TypeScript from `~/Git/GenomeHub/node_modules/typescript`, and you can set `TS_PATH` to point it somewhere else. `TRACE=1` prints each egglog iteration with the rules that matched most.

## Verdicts

- `CHEAT`: some class under the root holds `(Maybe z m)`. `m` is an undetermined `IndexQ` read, and `z` is a value the program wrote.
- `no cheat`: the run saturated, every node under the root has a meaning, and there was no finding.
- `UNDECIDED`: the run hit a limit, or some form under the root has no rule (an unknown method, an unresolved callee, unsupported syntax).

## Known limits

- Arithmetic is integer arithmetic, so `-0`, `NaN` and `Infinity` aren't modelled.
- Arrays are dense, records aren't modelled, and only straight-line blocks lower.
- A `filter` or `find` callback gets (element, index), not the array.
- The index-selection lemma (`find((_, k) => k === j)` reads `xs[j]`) only fires on an array the structural rules can't open, a variable.
- Callees aren't resolved yet, so `somefn() ?? 0` is UNDECIDED until the dumper inlines the body of `somefn`.
- Multiplying by a constant only folds when both sides are constants; `2 * i` stays an atom.
