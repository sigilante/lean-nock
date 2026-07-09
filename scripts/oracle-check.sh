#!/usr/bin/env bash
# Verdict-preservation check for the Class D oracle trial.
# `lake exec main` re-runs the 676-run sweep (26 programs x 26 subjects) and
# prints its signature.  Any change to Term, NT, phi, cw, or nockF that alters
# the trial's outcome will move this number.
#
# Expected: (632, 44, 0, 0)
#   632 agree | 44 two-sided `none` (the two designed-divergent programs)
#     0 mismatches | 0 asymmetries    <- the conviction columns
set -uo pipefail
EXPECTED='(632, 44, 0, 0)'
out="$(lake exec main 2>&1)" || { echo "lake exec main failed"; echo "$out"; exit 1; }
got="$(printf '%s\n' "$out" | grep -oE '\([0-9]+, [0-9]+, [0-9]+, [0-9]+\)' | tail -1)"
if [ "$got" != "$EXPECTED" ]; then
  echo "ORACLE SIGNATURE MISMATCH"
  echo "  expected: $EXPECTED"
  echo "  got:      ${got:-<none found>}"
  echo
  echo "A nonzero third or fourth component is a CONVICTION of the Class D"
  echo "schemas and must be reported under the TABLE-REPORT protocol, not fixed."
  exit 1
fi
echo "oracle sweep: $got  (0 mismatches, 0 asymmetries)"
