#!/usr/bin/env bash
# Print the axiom footprint of every theorem in the audit manifest.
# The build ALREADY enforces these (Nock/Audit.lean throws on drift); this
# script exists so a referee can see the footprints without reading Lean.
set -euo pipefail
lake build >/dev/null
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
{
  echo 'import Nock'
  grep -hoE '^#audit_clean .*' Nock/Audit.lean \
    | sed 's/^#audit_clean //' | tr ' ' '\n' | grep -v '^$' \
    | sed 's/^/#print axioms /'
} > "$tmp/Audit.lean"
LEAN_PATH=.lake/build/lib/lean lake env lean "$tmp/Audit.lean"
