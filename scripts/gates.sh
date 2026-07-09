#!/usr/bin/env bash
# Repository discipline gates.  Run by CI on every PR, and by hand:
#     ./scripts/gates.sh
# Exits nonzero on the first violation.  These enforce invariants that are
# stated in the README and relied on by the companion paper.
set -uo pipefail
fail=0
note() { printf '  %s\n' "$*"; }
bad()  { printf 'GATE FAILURE: %s\n' "$*"; fail=1; }

echo "== gate 1: no proof-chain module imports a quarantined module =="
for f in Nock/*.lean Nock.lean; do
  case "$f" in Nock/Oracle.lean|Nock/RuntimeBridge.lean) continue;; esac
  if grep -qE '^import Nock\.(Oracle|RuntimeBridge)' "$f"; then
    bad "$f imports a quarantined module"
  fi
done
[ $fail -eq 0 ] && note "ok — only Main.lean imports Oracle / RuntimeBridge"

echo "== gate 2: 'by native_decide' only in Nock/RuntimeBridge.lean =="
if grep -rnE 'by native_decide' Nock/ Main.lean Nock.lean 2>/dev/null \
     | grep -v '^Nock/RuntimeBridge.lean:' | grep -q .; then
  bad "native_decide outside RuntimeBridge"
  grep -rnE 'by native_decide' Nock/ Main.lean Nock.lean | grep -v '^Nock/RuntimeBridge.lean:'
else
  note "ok — $(grep -cE 'by native_decide' Nock/RuntimeBridge.lean) uses, all in RuntimeBridge"
fi

echo "== gate 3: panic! only inside 'partial def nock' (Nock/Basic.lean) =="
if grep -rn 'panic!' Nock/ Main.lean Nock.lean 2>/dev/null \
     | grep -v '^Nock/Basic.lean:' | grep -v '`panic' | grep -q .; then
  bad "panic! outside Nock/Basic.lean"
  grep -rn 'panic!' Nock/ Main.lean Nock.lean | grep -v '^Nock/Basic.lean:' | grep -v '`panic'
fi
if ! awk '/^partial def nock/{n=NR} /panic!/ && !/^ *--/ && !/`panic/ {if (!(n>0 && NR>n)) exit 1}' Nock/Basic.lean; then
  bad "a panic! in Nock/Basic.lean precedes 'partial def nock'"
fi
[ $fail -eq 0 ] && note "ok — every panic! is inside the runtime evaluator"

echo "== gate 4: no sorry, no axiom declarations =="
# `sorry` as a token, not a backticked prose mention and not a comment line.
# (Nock/Audit.lean also catches sorryAx structurally, at elaboration time.)
if grep -rnE '(^|[^`[:alnum:]_])sorry([^[:alnum:]_]|$)' Nock/ Main.lean Nock.lean 2>/dev/null \
     | grep -v '`' | grep -vE '^[^:]+:[0-9]+: *--' | grep -q .; then
  bad "sorry found"
  grep -rnE '(^|[^`[:alnum:]_])sorry([^[:alnum:]_]|$)' Nock/ Main.lean Nock.lean | grep -v '`' | grep -vE '^[^:]+:[0-9]+: *--'
fi
if grep -rn '^axiom' Nock/ Main.lean Nock.lean 2>/dev/null | grep -q .; then
  bad "axiom declaration found"
fi
[ $fail -eq 0 ] && note "ok — no sorry, no axiom declarations"

echo "== gate 5: the oracle is not in the proof chain =="
if grep -rnE '^import Nock\.Oracle' Nock/*.lean 2>/dev/null | grep -q .; then
  bad "a Nock/ module imports the oracle"
else
  note "ok — CsemF is referenced only in prose"
fi

if [ $fail -ne 0 ]; then echo; echo "GATES FAILED"; exit 1; fi
echo; echo "ALL GATES PASSED"
