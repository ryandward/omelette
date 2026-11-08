// Erasure oracle: checks omelette's verdicts against the definition of a cheat.
// Usage: node scripts/erasure.js FILE   (one expression per line, # comments; OMELETTE=binary)
//
// Each expression must mention `xs` only as `xs[i]`, so its value is c(xs[i]) for some c.
// It is a cheat iff the missing read's result c(undefined) is also the result of some present
// element. It may also mention `c` and `j`, a context fixed while the read varies: a cheat in
// any context is a cheat. The oracle evaluates c on a missing read and on a pool of present
// elements, in every context:
// - "no cheat" with a collision is unsound: the missing read is erased into a present one;
// - a cheat verdict with no collision may be the pool's limit, and is reported as a note.
// An expression whose result is the same for every element and the missing read never uses
// the read, so it erases nothing and is skipped.
// Elements are never undefined or null: omelette's model of an element excludes both.
const { execFileSync } = require('child_process');
const fs = require('fs');
const path = require('path');
const BIN = process.env.OMELETTE || path.join(__dirname, '..', 'target', 'release', 'omelette');

const POOL = [
  0, -0, 1, -1, 2, 0.5, NaN, Infinity, -Infinity,
  '', 'a', 'none', '0', '1', '-1', 'undefined', 'false', 'true', ' ',
  true, false,
  [], [0], [1], [''], [1, 2], [[]],
  {}, { length: -1 }, { length: 0 }, { length: 1 }, { valueOf: () => -1 }, { toString: () => '' },
  () => 0,
];

// Equal as results: SameValueZero on primitives (what === and includes cannot tell apart,
// with NaN equal to itself), element-wise on arrays.
const same = (a, b) =>
  Array.isArray(a) && Array.isArray(b)
    ? a.length === b.length && a.every((x, k) => same(x, b[k]))
    : a === b || (Number.isNaN(a) && Number.isNaN(b));
const show = (v) => {
  if (typeof v === 'function') return '<function>';
  if (v === undefined) return 'undefined';
  if (typeof v === 'number' && !Number.isFinite(v)) return String(v);
  if (Object.is(v, -0)) return '-0';
  try {
    return JSON.stringify(v);
  } catch {
    return String(v);
  }
};
const CONTEXTS = [true, false].flatMap((c) => [-1, 0, 1, 2].map((j) => [c, j]));
const run = (f, xs, [c, j]) => {
  try {
    return { value: f(xs, 0, c, j) };
  } catch (err) {
    return { throws: err.constructor.name };
  }
};

let unsound = 0;
let notes = 0;
const lines = fs.readFileSync(process.argv[2], 'utf8').split('\n').filter((l) => l.trim() && !l.startsWith('#'));
for (const e of lines) {
  if (/\bxs\b(?!\[i\])/.test(e)) {
    console.log(`${e}\n    skipped: mentions xs other than as xs[i]`);
    continue;
  }
  const f = new Function('xs', 'i', 'c', 'j', `return (${e});`);
  let collision;
  let missing;
  let used = false;
  for (const context of CONTEXTS) {
    const absent = run(f, [], context);
    if ('throws' in absent) continue; // A missing read that throws erases nothing.
    // Elements built from the missing result: an object whose length it is, or which it wraps.
    const pool = [...POOL, { length: absent.value }, [absent.value], { valueOf: () => absent.value }];
    const results = pool.map((v) => run(f, [v], context));
    // A result that is the same for every element and the missing read ignores the read.
    if (results.every((r) => !('throws' in r) && same(r.value, absent.value))) continue;
    used = true;
    missing = absent;
    const k = results.findIndex((r) => !('throws' in r) && same(r.value, absent.value));
    if (k >= 0) {
      collision = { element: pool[k], context };
      break;
    }
  }
  if (!used) continue;
  let out;
  try {
    out = execFileSync(BIN, [e], { encoding: 'utf8', timeout: 5000, maxBuffer: 1 << 28 });
  } catch (err) {
    out = (err.stdout || '') + (err.stderr || '');
  }
  const verdict = (out.match(/^verdict: (.*)$/m) || [])[1] || '?';
  if (verdict === 'no cheat' && collision !== undefined) {
    unsound++;
    const [c, j] = collision.context;
    console.log(`${e}\n    UNSOUND: no cheat, but with c=${c}, j=${j} element ${show(collision.element)} gives the missing read's result`);
  } else if (verdict.startsWith('CHEAT') && collision === undefined) {
    notes++;
    console.log(`${e}\n    note: ${verdict}, but in no context does a pooled element give the missing read's result (${show(missing.value)} in the last)`);
  }
}
console.log(`${unsound} unsound verdict(s), ${notes} uncorroborated cheat(s) in ${lines.length} expressions`);
process.exit(unsound ? 1 : 0);
