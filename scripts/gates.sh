#!/usr/bin/env bash
# Repository discipline gates.  Run by CI on every PR, and by hand:
#     ./scripts/gates.sh
# Exits nonzero on the first violation.  These enforce invariants that are
# stated in the README and relied on by the companion paper.
#
# These are textual gates.  The structural backstop for anything the paper
# cites is the audit manifest (Nock/Audit.lean, Main.lean), which inspects
# axiom footprints at elaboration time and cannot be fooled by spelling.  The
# gates exist to catch the same things in code the manifest does not reach.
set -uo pipefail
fail=0
note() { printf '  %s\n' "$*"; }
bad()  { printf 'GATE FAILURE: %s\n' "$*"; fail=1; }

# Every Lean source in the repository, excluding the build tree.
lean_files() { find . -name '*.lean' -not -path './.lake/*' | sort; }
# The proof chain: the library modules and the umbrella import.
chain_files() { ls Nock/*.lean Nock.lean; }

# Strip comments and backticked spans so that prose mentions do not trip the
# token gates.  Block comments (`/- ... -/`) are removed across lines, line
# comments (`-- ...`) are removed, and `code` spans are blanked.
strip_prose() {
  perl -0pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g; s{`[^`\n]*`}{``}g' "$1"
}

# An `import` directive, wherever it sits on the line and however it is
# modified: `import`, `public import`, `  import`, or several on one line.
quarantine_import_re='(^|[[:space:];])(public[[:space:]]+)?import[[:space:]]+Nock\.(Oracle|RuntimeBridge)([^[:alnum:]_.]|$)'
oracle_import_re='(^|[[:space:];])(public[[:space:]]+)?import[[:space:]]+Nock\.Oracle([^[:alnum:]_.]|$)'

echo "== gate 1: no proof-chain module imports a quarantined module =="
for f in $(chain_files); do
  case "$f" in Nock/Oracle.lean|Nock/RuntimeBridge.lean) continue;; esac
  if strip_prose "$f" | grep -qE "$quarantine_import_re"; then
    bad "$f imports a quarantined module"
  fi
done
[ $fail -eq 0 ] && note "ok — only executables import Oracle / RuntimeBridge"

echo "== gate 2: native_decide only in Nock/RuntimeBridge.lean =="
# Any spelling: `by native_decide`, `native_decide` after `;` or `<;>`,
# `decide +native`, `decide (config := { native := true })`, and the axioms it
# introduces used by hand.
native_re='native_decide|decide[[:space:]]*\+native|native[[:space:]]*:=[[:space:]]*true'
axiom_use_re='ofReduceBool|trustCompiler'
for f in $(lean_files); do
  case "$f" in ./Nock/RuntimeBridge.lean) continue;; esac
  if strip_prose "$f" | grep -nE "$native_re" | grep -q .; then
    bad "$f uses native_decide"
    strip_prose "$f" | grep -nE "$native_re" | sed "s|^|    $f:|"
  fi
  # Nock/Audit.lean names these axioms in its allow-list; everywhere else a
  # mention is a hand-rolled use.
  case "$f" in ./Nock/Audit.lean) continue;; esac
  if strip_prose "$f" | grep -nE "$axiom_use_re" | grep -q .; then
    bad "$f uses the native_decide axioms directly"
    strip_prose "$f" | grep -nE "$axiom_use_re" | sed "s|^|    $f:|"
  fi
done
[ $fail -eq 0 ] && note "ok — $(strip_prose Nock/RuntimeBridge.lean | grep -cE 'native_decide') uses, all in RuntimeBridge"

echo "== gate 3: panic! only inside 'partial def nock' (Nock/Basic.lean) =="
for f in $(lean_files); do
  case "$f" in ./Nock/Basic.lean) continue;; esac
  if strip_prose "$f" | grep -q 'panic!'; then
    bad "$f contains panic!"
  fi
done
if ! awk '/^partial def nock/{n=NR} /panic!/ && !/^ *--/ && !/`panic/ {if (!(n>0 && NR>n)) exit 1}' Nock/Basic.lean; then
  bad "a panic! in Nock/Basic.lean precedes 'partial def nock'"
fi
[ $fail -eq 0 ] && note "ok — every panic! is inside the runtime evaluator"

echo "== gate 4: no sorry, no admit, no axiom declarations =="
# `sorry` / `admit` as tokens: the tactic, the term `sorryAx`, and `admit`
# all elaborate to `sorryAx`, which the manifest also catches structurally.
sorry_re='(^|[^[:alnum:]_.])(sorry|sorryAx|admit)([^[:alnum:]_]|$)'
# `axiom` as a declaration keyword at any indentation, with any modifiers.
axiom_re='^[[:space:]]*((private|protected|noncomputable|unsafe|partial|public|@\[[^]]*\])[[:space:]]+)*axiom[[:space:]]'
for f in $(lean_files); do
  if strip_prose "$f" | grep -nE "$sorry_re" | grep -q .; then
    bad "$f contains sorry/admit"
    strip_prose "$f" | grep -nE "$sorry_re" | sed "s|^|    $f:|"
  fi
  if strip_prose "$f" | grep -nE "$axiom_re" | grep -q .; then
    bad "$f declares an axiom"
    strip_prose "$f" | grep -nE "$axiom_re" | sed "s|^|    $f:|"
  fi
done
[ $fail -eq 0 ] && note "ok — no sorry, no admit, no axiom declarations"

echo "== gate 5: the oracle is not in the proof chain =="
for f in $(chain_files); do
  case "$f" in Nock/Oracle.lean) continue;; esac
  if strip_prose "$f" | grep -qE "$oracle_import_re"; then
    bad "$f imports the oracle"
  fi
done
[ $fail -eq 0 ] && note "ok — CsemF is referenced only in prose"

echo "== gate 6: no trust escapes outside the quarantine =="
# `implemented_by`, `extern`, and `unsafe` let compiled code stand in for a
# definition the kernel never sees; `debug.skipKernelTC` disables the kernel.
escape_re='implemented_by|@\[extern|(^|[^[:alnum:]_])unsafe[[:space:]]|skipKernelTC'
for f in $(lean_files); do
  case "$f" in ./Nock/RuntimeBridge.lean|./Nock/Basic.lean) continue;; esac
  if strip_prose "$f" | grep -nE "$escape_re" | grep -q .; then
    bad "$f uses a trust escape"
    strip_prose "$f" | grep -nE "$escape_re" | sed "s|^|    $f:|"
  fi
done
[ $fail -eq 0 ] && note "ok — no implemented_by / extern / unsafe / skipKernelTC outside the quarantine"

if [ $fail -ne 0 ]; then echo; echo "GATES FAILED"; exit 1; fi
echo; echo "ALL GATES PASSED"
