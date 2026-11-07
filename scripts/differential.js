// Differential check against Node for closed expressions (no free variables).
// Usage: node scripts/differential.js FILE   (one expression per line, # comments)
// Prints every expression whose omelette value disagrees with Node, and exits 1 if any do.
// Open expressions (Node throws ReferenceError) are skipped: only their verdict is meaningful.
const { execFileSync } = require('child_process');
const fs = require('fs');
const path = require('path');
const BIN = path.join(__dirname, '..', 'target', 'release', 'omelette');
const NOT = Symbol('term');

function parse(tokens) {
  const t = tokens.shift();
  if (t !== '(') return t;
  const list = [];
  while (tokens[0] !== ')') list.push(parse(tokens));
  tokens.shift();
  return list;
}
function decode(x) {
  if (Array.isArray(x)) {
    if (x[0] !== 'cons') return NOT;
    const head = decode(x[1]);
    const tail = decode(x[2]);
    return head === NOT || !Array.isArray(tail) ? NOT : [head, ...tail];
  }
  if (/^-?\d+$/.test(x)) return Number(x);
  if (x.startsWith('utf16:')) {
    const hex = x.slice(6);
    let s = '';
    for (let i = 0; i < hex.length; i += 4) s += String.fromCharCode(parseInt(hex.slice(i, i + 4), 16));
    return s;
  }
  return { true: true, false: false, undefined: undefined, nan: NaN, nil: [] }.hasOwnProperty(x)
    ? { true: true, false: false, undefined: undefined, nan: NaN, nil: [] }[x]
    : NOT;
}
// omelette's values are finite, so a cyclic Node array is never equal to one.
const same = (a, b, open = new Set()) => {
  if (!Array.isArray(a) || !Array.isArray(b)) return Object.is(a, b);
  if (open.has(b)) return false;
  open.add(b);
  const equal = a.length === b.length && a.every((x, i) => same(x, b[i], open));
  open.delete(b);
  return equal;
};
const show = (v) => {
  if (v === NOT) return '<term>';
  if (typeof v === 'function') return '<function>';
  if (v === undefined) return 'undefined';
  try {
    return JSON.stringify(v);
  } catch {
    return '<cyclic>';
  }
};

let failures = 0;
const lines = fs.readFileSync(process.argv[2], 'utf8').split('\n').filter((l) => l.trim() && !l.startsWith('#'));
for (const e of lines) {
  let js;
  try {
    js = (0, eval)('(' + e + ')');
  } catch (err) {
    if (err instanceof ReferenceError || err instanceof SyntaxError) continue;
    js = { throws: err.constructor.name };
  }
  let out;
  try {
    out = execFileSync(BIN, [e], { encoding: 'utf8', timeout: 5000, maxBuffer: 1 << 28 });
  } catch (err) {
    out = (err.stdout || '') + (err.stderr || '');
    if (!/^consistency: /m.test(out)) {
      failures++;
      console.log(`${e}\n    omelette failed: ${err.code || err.signal || err.status}`);
      continue;
    }
  }
  if (/parse error/.test(out)) continue;
  const root = (out.match(/^root: (.*)$/m) || [])[1] || '?';
  const verdict = (out.match(/^verdict: (.*)$/m) || [])[1] || '?';
  const consistent = /^consistency: ok$/m.test(out);
  // An opaque run's root assumes what lowering does not model; it claims nothing.
  const opaque = /^opaque: yes/m.test(out);
  let value;
  try {
    value = decode(parse(root.replace(/\(/g, ' ( ').replace(/\)/g, ' ) ').trim().split(/\s+/)));
  } catch {
    value = NOT;
  }
  let problem = null;
  if (!consistent) problem = 'inconsistent graph';
  else if (value === NOT || opaque) problem = null; // An unresolved term claims no value.
  else if (js && js.throws) problem = `a value where Node throws ${js.throws}`;
  else if (!same(value, js)) problem = `${show(value)} where Node gives ${show(js)}`;
  if (problem) {
    failures++;
    console.log(`${e}\n    omelette gives ${problem} [${verdict}]`);
  }
}
console.log(`${failures} disagreement(s) in ${lines.length} expressions`);
process.exit(failures ? 1 : 0);
