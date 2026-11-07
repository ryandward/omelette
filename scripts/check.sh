#!/usr/bin/env bash
# Runs every case in tests/cases.txt (the absence verdict) and tests/mutations.txt (the mutation
# verdict) through omelette and compares the result with the expected one. Marks and fails a
# mismatch (!), a run that did not saturate (L), and an inconsistent graph (U).
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build --release -q
status=0
while IFS=$'\t' read -r file want e; do
  case "$want" in ''|'#'*) continue ;; esac
  out=$(./target/release/omelette "$e" 2>&1)
  line=verdict
  [ "$file" = mutations ] && line=mutation
  got=$(grep -m1 "^$line" <<<"$out" | sed "s/^$line: //; s/ (.*//")
  stats=$(grep -m1 '^egg:' <<<"$out" | sed 's/^egg: *//')
  mark=" "
  if [ "$got" != "$want" ]; then mark="!"; status=1; fi
  if ! grep -q 'stop: Saturated$' <<<"$stats"; then mark="L"; status=1; fi
  if grep -q '^consistency: inconsistent' <<<"$out"; then mark="U"; status=1; fi
  printf '%s %-10s %-64.64s %s\n' "$mark" "$got" "$e" "$stats"
done < <(sed 's/^/cases\t/' tests/cases.txt; sed 's/^/mutations\t/' tests/mutations.txt)
exit $status
