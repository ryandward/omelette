# Architecture

This is the target design for the rewrite in progress. The README describes what ships.

## The question

A cheat is an information flow in which a possibly missing read, written here as the absent value, is quietly swallowed or conflated with an ordinary value. The engine looks for these families:

| Family | The absent value becomes | Examples |
| --- | --- | --- |
| Default | a value the program wrote | `xs[i] ?? 0`, `xs[i] === undefined ? 0 : xs[i]`, `names[i] \|\| 'x'` |
| Unit absorption | the unit of a fold's monoid | `xs.slice(i, i + 1).every(p)`, `.some(p)`, `.join('')`, `.reduce(f, z)`, `.filter(p).length` |
| Container conflation | an empty collection | `groups.slice(i, i + 1).flat()`, `.flatMap(f)` |
| Coercion sink | whatever an operator makes of `undefined` | `names[i] === 'on'`, `widths[i] < 3`, `widths[i] + 1`, `names[i] + '!'`, `!names[i]` |
| Coordinate drift | a hole in a collection shaped like another | `users.map((_, i) => roles[i])`, `names.map((n, i) => names[i + 1])` |

Not cheats: the absence reaches the result unchanged (`names[i]`), stays visible in a container (`names.slice(i, i + 1).map(f)`), is observed rather than replaced (`names[i] === undefined`, or a present branch that ignores the element), the read throws instead of continuing (`names[i].length`), or the index is proven in range (`names.map((n, i) => names[i])`).

## Pipeline

```
source --oxc_parser--> AST --oxc_semantic--> symbols and references
       --lower (partial evaluation, JavaScript semantics)--> Core IR
       --egg (equational saturation, no runtime semantics)--> witnesses --> verdict
```

### Lowering: all of JavaScript's operational semantics

Lowering is a partial evaluator over a static value domain:

- **Known values**: integers, `NaN`, strings, booleans, `undefined`, lists of known length, and functions (parameters, body, captured environment).
- **Symbolic values**: a Core IR term with a static type (integer, string, boolean, list, or unknown, each marked defined or possibly undefined).
- **Splits**: a value that depends on whether one read is present. A read `xs[k]` not known to be in range lowers to a split whose absent side is `undefined` and whose present side is a fresh element variable `x`.

Operations evaluate on known values and build terms on symbolic ones. On a split, an operation applies to both sides: `widths[i] + 1` is a split whose absent side is `NaN` and whose present side is `x + 1`. Conditionals on a split lower each branch in both worlds, so narrowing falls out: in `names[i] !== undefined ? names[i] + '!' : 'none'`, the present world sees `x + '!'` and the absent world sees `'none'`. When a split leaves lowering, it becomes `Maybe(family, z, x. f, read)`. The family records the operation that first turned the absent side into a non-`undefined` value.

Lowering owns, and egg never sees:

- symbol identity and scope, through `oxc_semantic`;
- inlining of known functions with JavaScript arity: missing arguments are `undefined`, and walkers pass (element, index, array) and `reduce` passes (accumulator, element, index, array);
- unrolling literal lists of known length;
- typed operator dispatch: integer `+` is affine, string `+` is concatenation, and anything else is an uninterpreted operation that is never `undefined`;
- what each operator makes of `undefined` (the sinks);
- the provenance of walker indexes, for proving `names[i]` present inside `names.map` and for flagging drift;
- the preconditions on free variables: one used as an index, a bound, or an arithmetic operand is an integer, one used as a list is a dense list of defined elements, and any other is unknown and possibly undefined.

Unsupported syntax lowers to an `Unsupported` term, and unknown functions to an opaque `Call`.

### Core IR

A typed `egg::define_language!` enum. Integer arithmetic is affine and canonical. There are strings, booleans, lists (`Nil`, `Cons`, `Append`, `Slice`, `Len`), walkers over symbolic lists with bound bodies (`Map`, `Filter`, `Fold`, `Every`, `Some`, `Join`, `Flat`), reads `Read(xs, k)`, witnesses `Maybe(family, z, x. f, read)`, and drift escapes `Escape(read)`. egg performs no substitution.

### egg: equational laws only

- **Affine integer arithmetic** and interval bounds, so presence conditions can be compared.
- **Short lists**: a slice whose bounds differ by one has length at most one. A walker over a list `L` of length at most one is a witness over `Read(L, 0)` with the walker's unit: `Every` gives `true`, `Some` gives `false`, `Join` gives `''`, `Flat` gives `[]`, `Fold` gives the initial value, and a filter's length gives 0.
- **Presence context**: inside `Maybe(fam, z, x. f, r)`, a condition equivalent to `r` being present is `true` in `f` and `false` in `z`. This decides `xs.length ? xs[xs.length - 1] : 0`.
- **Projection**: a filter or find whose predicate is `index === j`, with `j` an integer, selects `Read(xs, j)`.

### Verdict

- A witness `Maybe(fam, z, x. f, r)` is a cheat of family `fam` when `r` is not proven present, `z` is not `undefined` and not a throw, `f` is not constant, and `z` is certain. A `z` that may itself be `undefined` makes the verdict UNDECIDED.
- `Escape(r)` with `r` not proven present is coordinate drift.
- With no cheat found, `Unsupported` or an opaque `Call` reaching the root makes the verdict UNDECIDED. Otherwise it is `no cheat`.

## Code shape

`Cargo.toml` and `clippy.toml` enforce pedantic Clippy, no dead code, functions of at most 60 lines, cognitive complexity of at most 15, and at most 5 arguments.
