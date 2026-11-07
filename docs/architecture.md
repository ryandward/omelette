# Architecture

## The question

A cheat is an information flow in which a read that may be missing is quietly swallowed or conflated with an ordinary value. The README lists the families: `default`, `unit`, `container`, `sink`, and `drift`. The first four leave a witness of the form `maybe z f (xs !? k)`: `z` where the read is missing, and `f` of the element where it is present. Drift leaves an `escape`: a read whose index came from another collection's walker, left as a possible hole in a mapped result.

## Pipeline

```
source --oxc_parser--> AST --oxc_semantic--> symbols, references, AST nodes
       --lower (partial evaluation)--> core IR, and whether it evaluated anything opaque
       --egg (equational saturation)--> classes --> witnesses --> verdict
```

Lowering decides every question of JavaScript's operational semantics: coercion, arity, method dispatch, effects, statement control flow, and which operations are modeled at all. The core IR is a small language with its own meaning, and egg proves equalities in that language only. Some of that meaning mirrors JavaScript where lowering needs it to: `eq` is strict equality, so `NaN` is unequal to itself; `text` is the text `join` writes for an element; and a `read` outside a list's bounds is `undefined`.

## Lowering: src/lower

A partial evaluator over a static value domain (`value.rs`):

- **Known values**: integers (affine forms with no atoms), `NaN`, strings as UTF-16 code units, booleans, `undefined`, a thrown error, lists of known length, and functions (parameters, body, and the bindings they closed over).
- **Symbolic values**: a core term with a static type: integer (an affine form over atoms), boolean, string, list, defined, or possibly undefined. A list's type records whether its elements may be `undefined`. A free list's elements are defined by the model's precondition. A built list's elements are defined when every value put into it is; for `[undefined, ...ys]`, or a map whose callback may return `undefined`, they are not. An element of such a list binds to an `item` variable, not an `elem` one.
- **Splits**: a value that depends on whether one read is present. A read of a symbolic list at an index not proven in range lowers to a split whose absent side is `undefined` and whose present side is the read's element binder. Every split on one read shares one binder.
- **Short lists**: a symbolic list of at most one element, from a slice whose bounds differ by one, `slice(-1)`, or a filter whose predicate is `index === j` (a projection). Each one carries its element slot, the element's value there, whether a filter keeps it, and whether the slot's index came from another collection's walker.

Operations are typed (`ops.rs`):

- Integer arithmetic stays affine, and a form whose constant or any coefficient exceeds 2^53 - 1 is not folded.
- `+` concatenates when an operand is a string or a list, and otherwise adds, with booleans coerced. An `undefined` or `NaN` operand gives `NaN` only next to an operand that `+` would add.
- Ordering against `undefined` is `false`. Two lists or functions lowering built are strictly equal only if they are one object.
- An operation on a value of unknown type becomes an uninterpreted `dyn` term that is never `undefined`. The one exception is `x ?? y` of an unknown `x` with a fallback that may itself be `undefined`, which becomes `dyn?`.

Every operation lifts over splits: it applies on both sides, each in its own world with the split's read narrowed. A split's family is the last operation that wrote its absent side, with two qualifications. An operation that only passes values through (a read, `length`, a spread) keeps the family it was given. An undecided step, `===` against or `??` toward an unknown, leaves the whole chain undecided, since for some value of the unknown the chain only tests presence. Branches (`expr.rs`) lower each arm in every world of the splits in their test. Presence tests, `&&`, `||`, and `??` all narrow this way, and a binding's value, or a literal list's item, settles to the worlds the enclosing branches decided when it is used. A conditional on a symbolic test that is not a split swallows nothing itself; egg labels it a default if the test proves to be the read's own presence test.

Effects are strict. Array elements, a call's callee or receiver and arguments, `const` initializers, and binary operands are evaluated before what follows: lowering runs what follows on the values as they are, then makes every world in which one of them throws throw. Calling a value that is not a function, or reading a property of `undefined`, throws. Lowering also reports whether it evaluated anything opaque: a construct it does not model, a call it could not resolve, a walker over an unknown callback, or a spread of a value of unknown type. Any of these may throw or loop, so the expression's value is unknown even where its term does not mention them.

Calls (`calls.rs`) inline known functions with JavaScript's arity, and run statement lists to their first `return`, so a branch that does not return continues with the statements after it. Array patterns destructure by iteration, so a string yields its code points. Methods dispatch on what lowering knows about the receiver, after the checks JavaScript makes first: a callback that is not a function throws, and `flat` is modeled at depth one, or zero, which copies.

- A literal list unrolls `map`, `filter`, `find`, `every`, `some`, `reduce`, `join`, `flat`, `flatMap`, `slice` with known bounds, `at`, and `concat`. `filter` appends each element where its keep holds, as a conditional where the keep is symbolic. A separator that may be missing writes the default comma there.
- A short list yields a split whose absent side is the method's unit: `true` for `every`, `false` for `some`, `''` for `join`, `[]` for `flat` and `flatMap`, the initial value for `reduce` (a throw without one), and `0` for a filtered count.
- A symbolic list yields a term. `map`, `filter`, `every`, `some`, and `reduce` (as `fold`) carry their callback, lowered once with fresh element and index binders. `join` and `flat` take the list alone. A fold seed that may be missing flows into the accumulator, where the callback may or may not swallow it, so that flow is undecided.

Before falling back to a term, lowering recognizes a filter or find whose predicate is `index === j` with `j` an integer, and a `reduce` whose callback ignores its accumulator. A callback that ignores its accumulator yields its value on the last element. Without an initial value, a one-element list returns that element without calling the callback, so the law then also requires the callback to return its element. Reading a mapped list applies its callback to the underlying read, with that read's element, index, and list, as `map` would. A short list's callbacks likewise run in the world where its slot is present.

`oxc_semantic` provides symbol identity for inlining and for recognizing a projection's index parameter. `usage.rs` uses its node tree to give each free variable its precondition, looking through parentheses and type assertions. A walker's index binder records the list it ranges over. Inside the callback of a walker over `L`, a read of a list `M` is proven in range in two cases, provided `L` is provably no longer than `M`:

- at `L`'s own index;
- at `M`'s first or last element, since the callback runs only on a non-empty list (as does a mapped read's callback, or a short list's, where its read is present).

`L` is provably no longer than `M` when `M` is `L` itself, or is reached from `L` through `map`, `filter`, `slice`, `append`, or a full copy. A read at any other coordinate derived from a walker's index is marked as drift. When such a read reaches a map's result with its absent side still `undefined`, it is emitted as `escape`.

A split leaves lowering as `maybe(family, z, x. f, read, has)`, or as the read itself when it is still `undefined` where missing and the element where present. `has(xs, k)` is the read's own presence test: the read's class also holds its value, and a present element that is `undefined` shares that class with every missing read.

## Core IR: src/core.rs

A typed `egg::define_language!` enum:

- constants, including `throw` and the tagged `unsupported`;
- canonical affine sums (`lin`), products of atoms (`mul`), integer order (`le`, `lt`), and booleans;
- strict equality (`eq`), strings (`concat`, and `text`);
- lists (`nil`, `cons`, `append`, `slice`, `len`);
- walkers over symbolic lists (`map`, `filter`, `every`, `some`, `fold` with bound callbacks; `join` and `flat`);
- reads that may be missing (`read`), reads proven in range (`at`), and presence tests (`has`);
- witnesses (`maybe`), their untagged values (`elim`), and drift escapes (`escape`), each with its read's `has`;
- `dyn`, `dyn?`, and `call`.

egg never substitutes into a lambda.

## egg: src/engine

The analysis (`analysis.rs`) tracks known constants and integer bounds. Lengths and walker indices are non-negative. A slice whose bounds differ by `d >= 0` holds at most `d` elements, and a conditional lies between its branches. A class proven to hold two constants, or an empty interval, marks the graph inconsistent. A read's presence is the constant value of its `has`, never the value it reads. The rules (`rules.rs`) are:

- boolean and conditional identities, and the normal forms `a < b` as `0 <= b - a - 1` and `a <= b` as `0 <= b - a`, with sums kept in canonical order;
- `read(xs, k)` expands to `if(has(xs, k), at(xs, k), undefined)`, `has(xs, k)` to `0 <= k and k < len(xs)`, and `at(cons(h, t), 0)` is `h`;
- list identities: lengths of `nil`, `cons`, `append`, `map`, and a conditional; appends of `nil` and `cons`; walkers over `nil`; and a filter whose predicate is `false`;
- `[...a, z][0]` is `maybe(default, z, id, a[0])`, and `[z, ...xs][xs.length]` is `maybe(default, z, id, xs[len - 1])`;
- presence context: in a witness whose `z`, or the body of whose `f`, is a conditional on its own `has`, that conditional is its else branch in `z` and its then branch in `f`; when the witness was propagating and the else branch is not `undefined`, the program wrote that branch as a default;
- a witness whose `has` is `false` is its `z`; one whose `has` is `true` is its present branch where that is a constant, and its read where that is the element;
- every `maybe` implies the untagged `elim` of the same value, so spellings that reach one value through different flows share a class.

Detection (`detect.rs`) walks the classes the root's value depends on. It skips a class with a known constant, a decided conditional's dead arm, a witness's side its decided `has` rules out, and a walker's callback over an empty list. A witness or escape counts only if the root has no representative that avoids its class. Detection judges each class's witnesses together, one group per read. Witnesses in one class over one read denote one value: their replacements agree where the read is missing, and their present branches agree on every element. A proof from one representative therefore holds for the whole group: that the branch does not mention the element, that it is free of unknowns, or that the replacement is certainly a value with no throw in it. A branch that avoids the element only by reading the same free list another way may be reading that element, so it is undecided rather than an observation. A witness whose binder is an `item` stays undecided too, since its branch may vary only at the `undefined` element. The README's verdict section states the conditions.

## Code shape

`Cargo.toml` and `clippy.toml` deny pedantic Clippy findings and dead code, and cap functions at 60 lines, cognitive complexity at 15, and arguments at 5.
