#!/usr/bin/env bash
# Runs every case in tests/cases.txt through omelette and compares the verdict with the expected
# one. Exits 1 on any mismatch, or if a run reports an unsound merge.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build --release -q
status=0
while IFS=$'\t' read -r want e; do
  case "$want" in ''|'#'*) continue ;; esac
  out=$(./target/release/omelette "$e" 2>&1)
  got=$(grep -m1 '^verdict' <<<"$out" | sed 's/^verdict: //; s/ (.*//')
  stats=$(grep -m1 '^egglog:' <<<"$out" | sed 's/^egglog: *//')
  mark=" "
  if [ "$got" != "$want" ]; then mark="!"; status=1; fi
  if grep -q '^consistency: UNSOUND' <<<"$out"; then mark="U"; status=1; fi
  printf '%s %-10s %-64.64s %s\n' "$mark" "$got" "$e" "$stats"
done < tests/cases.txt
exit $status
