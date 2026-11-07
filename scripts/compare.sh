#!/usr/bin/env bash
# Runs every expression in tests/cases.txt through both engines and prints the two verdicts side
# by side. Exits 1 if any verdict differs, or if the egglog engine reports an unsound merge.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build --release -q
status=0
while IFS= read -r e; do
  [ -z "$e" ] && continue
  new=$(./target/release/omelette "$e" 2>&1)
  old=$(./target/release/egg-gate "$e" 2>&1)
  nv=$(grep -m1 '^verdict' <<<"$new" | sed 's/^verdict: //; s/ (.*//')
  ov=$(grep -m1 '^verdict' <<<"$old" | sed 's/^verdict: //; s/ (.*//')
  stats=$(grep -m1 '^egglog:' <<<"$new" | sed 's/^egglog: *//')
  mark=" "
  if [ "$nv" != "$ov" ]; then mark="!"; status=1; fi
  if grep -q '^consistency: UNSOUND' <<<"$new"; then mark="U"; status=1; fi
  printf '%s %-10s %-10s %-64.64s %s\n' "$mark" "$nv" "$ov" "$e" "$stats"
done < tests/cases.txt
exit $status
