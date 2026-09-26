# Differential testing against NockVM

This directory runs lean-nock's compiled formulas through Nockchain's
production interpreter, NockVM, and compares verdicts. It is evidence, not
proof. The theorems in `Nock/` are about lean-nock's semantics; this checks
that the semantics, and the formulas the compilers emit, behave the same on a
production runtime.

```sh
NOCKCHAIN_ROOT=/path/to/nockchain python3 diff/run.py
```

Requirements: a Nockchain checkout (for `crates/nockvm/rust/{nockvm,ibig}`),
the Rust toolchain pinned in `nockvm-oracle/rust-toolchain.toml` (which
matches Nockchain's pin), and cargo access to crates.io. The main CI job does
not run this, since it needs a Nockchain checkout.

## What runs

`ExportCorpus.lean` (`lake exe export-corpus`) emits every case with the
verdict lean-nock's fuel interpreter assigns it:

| group | cases |
| --- | --- |
| `word` | all 13 Λ words (Tables A–C, `add` and `sub` included) × 155 stacks |
| `classd` | the 26 Class D oracle programs × 26 subjects |
| `rec` | self- and mutual recursion, and each Class D `while` re-encoded as a recursive definition, × 26 subjects |
| `gate` | each Class D program packaged as a gate core, fired with `[9 2 0 1]` |
| `hint` | six programs wrapped in a static hint, a constant-clue hint, and a crashing-clue hint |
| `order` | evaluation-order races: a crashing operand against a diverging one, for every multi-operand rule |
| `known` | opcode-10 edits at an invalid axis, where NockVM is known to panic. Λ never emits these; they show the harness catches a real divergence, and track the finding. Reported separately; they do not fail the run |

`nockvm-oracle/` is a small Rust binary that evaluates each program with no
jets warm (pure Nock) under an op budget. It reports `CRASH` only for a
deterministic `%exit`, and `BUDGET` for budget exhaustion, so divergence and
crashing stay distinct. A Rust panic is reported as `PANIC`.

## Reading the results

`results/RESULTS.md` summarizes the latest run; `results/results.tsv` has
every case. `TIMEOUT` (lean-nock, fuel exhausted) against `BUDGET` (NockVM,
budget exhausted) counts as agreement: both are consistent with divergence,
and neither proves it. Any other difference is a mismatch, and the script
exits nonzero.
