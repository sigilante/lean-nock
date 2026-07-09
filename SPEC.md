# SPEC: lean-nock Outcome Refactor

**Status:** approved for implementation. Design decisions in this document are
final — implement them as written. If a proof cannot be closed as specified,
stop and report; do not redesign the semantics to make a proof easier.

**Toolchain:** Lean 4.28.0 (pinned in `lean-toolchain`). No Mathlib. No new
dependencies. `lake build` must succeed with zero warnings treated as your
smoke test after every phase.

---

## 1. Problem statement (why this refactor exists)

The current `NockEval : Noun → Noun → Noun → Prop` relation is **unsound with
respect to Nock crash semantics**. Root cause: `fas`, `hax`, `lus`, `tis` are
total functions whose crash arms are `panic!`. In Lean's logic, `panic!`
reduces to `Inhabited.default`, and `default : Noun = atom 0`. Consequently:

- `NockEval a (cell (atom 0) (atom 0)) (atom 0)` is derivable for every `a`
  (axis 0 must crash; the relation certifies it returns `0`).
- `NockEval.op4` derives increment-of-cell `= atom 0`.
- The dec underflow guard's crash branch `[0 0]` "evaluates" to `atom 0`, so
  the kernel will certify decrement-of-zero returning zero.

The fix: crashes become an explicit outcome. Divergence remains represented by
**absence of a derivation** (standard for big-step semantics) and becomes
*statable* via the fuel interpreter.

Design target (from the companion paper): outcomes are three-valued —
value, deterministic crash (`exit`), divergence (no derivation / fuel
exhaustion at every fuel).

---

## 2. Phase 0 — Option-valued primitives

**File:** `Nock/Basic.lean` (modify in place).

Keep `Noun`, `wut` unchanged. Replace the panicking primitives with
Option-valued totals. Delete `lus`, `tis`, `fas`, `hax` as proof-facing
definitions; the `partial def nock` evaluator (testing only) is updated to
call the new primitives and panic **at its own call sites** on `none`.
After this phase, `grep -n "panic" Nock/*.lean` must show hits only inside
`partial def nock`.

```lean
-- +: increment. none on cell.
def lusO : Noun → Option Noun
  | atom a   => some (atom (1 + a))
  | cell _ _ => none

-- =: equality of two nouns. Total (the relation always supplies two nouns).
def tisN (a b : Noun) : Noun := if a = b then atom 0 else atom 1

-- /: tree address. none on axis 0, axis into an atom, or cell axis.
def fasO : Noun → Noun → Option Noun
  | atom 0, _        => none
  | atom 1, a        => some a
  | atom 2, atom _   => none
  | atom 2, cell a _ => some a
  | atom 3, atom _   => none
  | atom 3, cell _ b => some b
  | atom (n + 4), b  =>
      match fasO (atom ((n + 4) / 2)) b with
      | some (cell hd tl) => if (n + 4) % 2 = 0 then some hd else some tl
      | some (atom _)     => none
      | none              => none
  | cell _ _, _      => none
termination_by axis _ => match axis with | atom n => n | cell _ _ => 0

-- #: tree edit. none propagated from fasO or on axis 0 / non-atom axis.
def haxO : Noun → Noun → Noun → Option Noun
  | atom 0, _, _       => none
  | atom 1, a, _       => some a
  | atom (n + 2), b, c =>
      let a : Nat := (n + 2) / 2
      if (n + 2) % 2 = 0 then
        match fasO (atom (a + a + 1)) c with
        | some sib => haxO (atom a) (cell b sib) c
        | none     => none
      else
        match fasO (atom (a + a)) c with
        | some sib => haxO (atom a) (cell sib b) c
        | none     => none
  | cell _ _, _, _     => none
termination_by axis _ _ => match axis with | atom n => n | cell _ _ => 0
```

**File:** `Nock/Proofs.lean` — port the lemma library 1:1. Same names with
`O` suffix, same proof recipes (`omega` bridge, `simp only [fasO, h]`,
`rw [if_pos/if_neg]`). Required lemmas (statements are normative):

```lean
theorem fasO_one  (a : Noun)     : fasO (atom 1) a = some a
theorem fasO_head (a b : Noun)   : fasO (atom 2) (cell a b) = some a
theorem fasO_tail (a b : Noun)   : fasO (atom 3) (cell a b) = some b
theorem fasO_rec_even (n : Nat) (b a c : Noun)
    (h : fasO (atom (n + 2)) b = some (cell a c)) :
    fasO (atom (2 * (n + 2))) b = some a
theorem fasO_rec_odd  (n : Nat) (b a c : Noun)
    (h : fasO (atom (n + 2)) b = some (cell a c)) :
    fasO (atom (2 * (n + 2) + 1)) b = some c
theorem fasO_four  (a b c : Noun) : fasO (atom 4) (cell (cell a b) c) = some a
theorem fasO_five  (a b c : Noun) : fasO (atom 5) (cell (cell a b) c) = some b
theorem fasO_six   (a b c : Noun) : fasO (atom 6) (cell a (cell b c)) = some b
theorem fasO_seven (a b c : Noun) : fasO (atom 7) (cell a (cell b c)) = some c
theorem haxO_one (a b : Noun)     : haxO (atom 1) a b = some a
theorem haxO_rec_even (a : Nat) (b c : Noun) ...   -- mirror old hax_rec_even
theorem haxO_rec_odd  (a : Nat) (b c : Noun) ...   -- mirror old hax_rec_odd
theorem haxO_two   (b c : Noun) : haxO (atom 2) b c = some (cell b (fasO (atom 3) c).get!) -- NO: see below
theorem haxO_six (b bat sam ctx : Noun) :
    haxO (atom 6) b (cell bat (cell sam ctx)) = some (cell bat (cell b ctx))
```

**Correction to the above:** never use `.get!` (it reintroduces
panic/default). State `haxO_two`/`haxO_three` conditionally, matching the
old conditional style:

```lean
theorem haxO_two (b c t : Noun) (h : fasO (atom 3) c = some t) :
    haxO (atom 2) b c = some (cell b t)
theorem haxO_three (b c h2 : Noun) (h : fasO (atom 2) c = some h2) :
    haxO (atom 3) b c = some (cell h2 b)
```

`haxO_six` is unconditional (the gate shape guarantees the sibling lookups
succeed) and is the load-bearing lemma for all gate-call proofs. Prove it by
the same rewrite chain as before: `haxO_rec_even 2`, `fasO_seven`,
`haxO_rec_odd 0`, `fasO_head`, `haxO_one`.

**Acceptance (Phase 0):** `lake build` clean; all lemmas above proved without
`sorry`; `panic` only inside `partial def nock`.

---

## 3. Phase 1 — `Outcome` and the new `NockEval`

**File:** `Nock/Eval.lean` — full replacement. Delete the old relation
entirely; do not keep both (drift risk).

```lean
inductive Outcome
  | val  : Noun → Outcome
  | exit : Outcome
  deriving DecidableEq, Repr
```

Semantics conventions (normative):

- **Divergence = no derivation.** There is no `Outcome` constructor for it.
- **Evaluation order is left-to-right and strict**, matching Vere/NockVM:
  a crash in an earlier operand hides later operands. This is what makes
  determinism true. Crash-propagation constructors below encode exactly this
  order; do not add symmetric variants.
- **Tail-position subcomputations pass their `Outcome` through** (the `o`
  pattern below). Only intermediate results consumed by the rule need a
  `.val` hypothesis plus an explicit crash constructor.
- Opcode 6 keeps the **semantic reading** (not the macro expansion), now with
  the non-loobean crash case — Nock 4K's opcode 6 crashes on any test result
  other than `0`/`1`. Equivalence to the macro form is out of scope.
- Opcode 9 keeps the **one-step unfolding** `*[a 9 b c] = *[core /[b core]]`.

Malformedness predicate (decidable, as `Bool`):

```lean
def Malformed : Noun → Bool
  | atom _ => true                       -- atom formula crashes
  | cell (cell _ _) _ => false           -- autocons: always well-formed
  | cell (atom k) t =>
    match k, t with
    | 0, _ => false
    | 1, _ => false
    | 2, cell _ _ => false | 2, _ => true
    | 3, _ => false
    | 4, _ => false
    | 5, cell _ _ => false | 5, _ => true
    | 6, cell _ (cell _ _) => false | 6, _ => true
    | 7, cell _ _ => false | 7, _ => true
    | 8, cell _ _ => false | 8, _ => true
    | 9, cell _ _ => false | 9, _ => true
    | 10, cell (cell _ _) _ => false | 10, _ => true
    | 11, cell _ _ => false | 11, _ => true
    | _, _ => true                       -- opcode ≥ 12
```

The relation (complete constructor list — implement verbatim, names are API):

```lean
inductive NockEval : Noun → Noun → Outcome → Prop where
  -- malformed formulas crash deterministically
  | crash_malformed {a f} (h : Malformed f = true) :
      NockEval a f .exit

  -- *[a [b c] d] = [*[a b c] *[a d]]
  | autocons {a b c fol r1 r2} :
      NockEval a (cell b c) (.val r1) →
      NockEval a fol (.val r2) →
      NockEval a (cell (cell b c) fol) (.val (cell r1 r2))
  | autocons_crashL {a b c fol} :
      NockEval a (cell b c) .exit →
      NockEval a (cell (cell b c) fol) .exit
  | autocons_crashR {a b c fol r1} :
      NockEval a (cell b c) (.val r1) →
      NockEval a fol .exit →
      NockEval a (cell (cell b c) fol) .exit

  -- *[a 0 b] = /[b a]
  | op0 {a fol r} (h : fasO fol a = some r) :
      NockEval a (cell (atom 0) fol) (.val r)
  | op0_crash {a fol} (h : fasO fol a = none) :
      NockEval a (cell (atom 0) fol) .exit

  -- *[a 1 b] = b
  | op1 {a fol} :
      NockEval a (cell (atom 1) fol) (.val fol)

  -- *[a 2 b c] = *[*[a b] *[a c]]
  | op2 {a b c r1 r2 o} :
      NockEval a b (.val r1) →
      NockEval a c (.val r2) →
      NockEval r1 r2 o →
      NockEval a (cell (atom 2) (cell b c)) o
  | op2_crashL {a b c} :
      NockEval a b .exit →
      NockEval a (cell (atom 2) (cell b c)) .exit
  | op2_crashR {a b c r1} :
      NockEval a b (.val r1) →
      NockEval a c .exit →
      NockEval a (cell (atom 2) (cell b c)) .exit

  -- *[a 3 b] = ?*[a b]
  | op3 {a fol r} :
      NockEval a fol (.val r) →
      NockEval a (cell (atom 3) fol) (.val (wut r))
  | op3_crash {a fol} :
      NockEval a fol .exit →
      NockEval a (cell (atom 3) fol) .exit

  -- *[a 4 b] = +*[a b]
  | op4 {a fol r v} :
      NockEval a fol (.val r) →
      lusO r = some v →
      NockEval a (cell (atom 4) fol) (.val v)
  | op4_cell {a fol r} :
      NockEval a fol (.val r) →
      lusO r = none →
      NockEval a (cell (atom 4) fol) .exit
  | op4_crash {a fol} :
      NockEval a fol .exit →
      NockEval a (cell (atom 4) fol) .exit

  -- *[a 5 b c] = =[*[a b] *[a c]]
  | op5 {a b c r1 r2} :
      NockEval a b (.val r1) →
      NockEval a c (.val r2) →
      NockEval a (cell (atom 5) (cell b c)) (.val (tisN r1 r2))
  | op5_crashL {a b c} :
      NockEval a b .exit →
      NockEval a (cell (atom 5) (cell b c)) .exit
  | op5_crashR {a b c r1} :
      NockEval a b (.val r1) →
      NockEval a c .exit →
      NockEval a (cell (atom 5) (cell b c)) .exit

  -- *[a 6 b c d]: semantic if-then-else, crash on non-loobean test
  | op6_then {a b c d o} :
      NockEval a b (.val (atom 0)) →
      NockEval a c o →
      NockEval a (cell (atom 6) (cell b (cell c d))) o
  | op6_else {a b c d o} :
      NockEval a b (.val (atom 1)) →
      NockEval a d o →
      NockEval a (cell (atom 6) (cell b (cell c d))) o
  | op6_nonloob {a b c d r} :
      NockEval a b (.val r) →
      r ≠ atom 0 → r ≠ atom 1 →
      NockEval a (cell (atom 6) (cell b (cell c d))) .exit
  | op6_crash {a b c d} :
      NockEval a b .exit →
      NockEval a (cell (atom 6) (cell b (cell c d))) .exit

  -- *[a 7 b c] = *[*[a b] c]
  | op7 {a b c r1 o} :
      NockEval a b (.val r1) →
      NockEval r1 c o →
      NockEval a (cell (atom 7) (cell b c)) o
  | op7_crash {a b c} :
      NockEval a b .exit →
      NockEval a (cell (atom 7) (cell b c)) .exit

  -- *[a 8 b c] = *[[*[a b] a] c]
  | op8 {a b c r1 o} :
      NockEval a b (.val r1) →
      NockEval (cell r1 a) c o →
      NockEval a (cell (atom 8) (cell b c)) o
  | op8_crash {a b c} :
      NockEval a b .exit →
      NockEval a (cell (atom 8) (cell b c)) .exit

  -- *[a 9 b c] = *[core /[b core]]  (one-step unfolding of the spec)
  | op9 {a b c core arm o} :
      NockEval a c (.val core) →
      fasO b core = some arm →
      NockEval core arm o →
      NockEval a (cell (atom 9) (cell b c)) o
  | op9_badaxis {a b c core} :
      NockEval a c (.val core) →
      fasO b core = none →
      NockEval a (cell (atom 9) (cell b c)) .exit
  | op9_crash {a b c} :
      NockEval a c .exit →
      NockEval a (cell (atom 9) (cell b c)) .exit

  -- *[a 10 [b c] d] = #[b *[a c] *[a d]]  (evaluate c, then d)
  | op10 {a b c d r1 r2 v} :
      NockEval a c (.val r1) →
      NockEval a d (.val r2) →
      haxO b r1 r2 = some v →
      NockEval a (cell (atom 10) (cell (cell b c) d)) (.val v)
  | op10_badaxis {a b c d r1 r2} :
      NockEval a c (.val r1) →
      NockEval a d (.val r2) →
      haxO b r1 r2 = none →
      NockEval a (cell (atom 10) (cell (cell b c) d)) .exit
  | op10_crashL {a b c d} :
      NockEval a c .exit →
      NockEval a (cell (atom 10) (cell (cell b c) d)) .exit
  | op10_crashR {a b c d r1} :
      NockEval a c (.val r1) →
      NockEval a d .exit →
      NockEval a (cell (atom 10) (cell (cell b c) d)) .exit

  -- *[a 11 t c] = *[a c]   (static hint, atom tag)
  | op11_static {a t c o} :
      NockEval a c o →
      NockEval a (cell (atom 11) (cell (atom t) c)) o
  -- *[a 11 [t c] d]: hint computation must produce a value, then d in tail
  | op11_dynamic {a t c d r1 o} :
      NockEval a c (.val r1) →
      NockEval a d o →
      NockEval a (cell (atom 11) (cell (cell t c) d)) o
  | op11_dyn_crash {a t c d} :
      NockEval a c .exit →
      NockEval a (cell (atom 11) (cell (cell t c) d)) .exit
```

Port the sanity examples at the bottom of the old `Eval.lean`, adjusting to
`.val` and the `fasO` hypothesis style, e.g.:

```lean
example (a : Noun) : NockEval a (cell (atom 0) (atom 1)) (.val a) :=
  NockEval.op0 (fasO_one a)
```

Add these new sanity checks (they are the point of the refactor):

```lean
-- Axis 0 crashes — previously derivable as (atom 0).
example (a : Noun) : NockEval a (cell (atom 0) (atom 0)) .exit :=
  NockEval.op0_crash rfl
-- Increment of a cell crashes — previously derivable as (atom 0).
example : NockEval (atom 0)
    (cell (atom 4) (cell (atom 1) (cell (atom 1) (atom 2)))) .exit :=
  NockEval.op4_cell NockEval.op1 rfl
```

**Acceptance (Phase 1):** builds; old relation deleted; sanity examples pass.

---

## 4. Phase 2 — Fuel interpreter, soundness, completeness, determinism

**New file:** `Nock/Fuel.lean`.

```lean
-- none = fuel exhausted (no verdict). some .exit = deterministic crash.
def nockF : Nat → Noun → Noun → Option Outcome
```

Structure: `nockF 0 _ _ = none`; at `fuel+1`, match the formula exactly along
the constructor lines of `NockEval` (including `Malformed f = true → some
.exit`), recursing at `fuel`. Every recursive call decrements. Use nested
`match` on the recursive results (`none → none`, `some .exit → some .exit`
per the propagation constructors, `some (.val r) → continue`). Do **not**
introduce a monad instance; explicit matches keep the soundness induction
syntactic.

Theorems, in dependency order (statements normative):

```lean
theorem nockF_sound {k a f o} (h : nockF k a f = some o) : NockEval a f o
-- Induction on k; cases on f mirror the interpreter's match tree.

theorem nockF_mono {k k' a f o} (h : nockF k a f = some o) (hk : k ≤ k') :
    nockF k' a f = some o
-- Induction on k generalizing everything; the standard fuel-monotonicity bash.

theorem nockF_complete {a f o} (h : NockEval a f o) :
    ∃ k, nockF k a f = some o
-- Induction on the derivation. Each case: obtain fuels from the IHs, take
-- max + 1, lift each with nockF_mono, assemble. This is the labor-heavy
-- proof (~30 cases, all mechanical).

theorem NockEval.deterministic {a f o₁ o₂}
    (h₁ : NockEval a f o₁) (h₂ : NockEval a f o₂) : o₁ = o₂ := by
  obtain ⟨k₁, hk₁⟩ := nockF_complete h₁
  obtain ⟨k₂, hk₂⟩ := nockF_complete h₂
  have e₁ := nockF_mono hk₁ (Nat.le_max_left  k₁ k₂)
  have e₂ := nockF_mono hk₂ (Nat.le_max_right k₁ k₂)
  simp [e₁] at e₂; exact e₂
-- NOTE: determinism is a corollary via the interpreter — do NOT attempt the
-- direct double-induction with constructor-disjointness case analysis.

def Diverges (a f : Noun) : Prop := ∀ o, ¬ NockEval a f o

theorem diverges_iff_fuel (a f : Noun) :
    Diverges a f ↔ ∀ k, nockF k a f = none
-- (→) contrapositive via nockF_sound. (←) contrapositive via nockF_complete.
```

**Acceptance (Phase 2):** all four theorems + `diverges_iff_fuel` proved, no
`sorry`; `#print axioms NockEval.deterministic` shows only `propext`,
`Quot.sound` (and possibly `Classical.choice` from `simp` — acceptable).

---

## 5. Phase 3 — Port the dec development

**File:** `Nock/HoonOne.lean`.

1. **Quarantine `native_decide`.** Move `decGate`, `decGate'`, `decGate_eq`,
   `decBat_eq` into a new file `Nock/RuntimeBridge.lean` with a header
   comment: "runtime/prover bridge; depends on `Lean.ofReduceBool` via
   `native_decide`; nothing in the proof chain may import this file."
   Nothing else imports it. `Main.lean` may.
2. **Kill `native_decide` in the proof chain.** `guardBody_parts` and
   `pushLoop_parts` are equalities between concrete `n!` literals and
   constructor expressions. Replace `native_decide` with, in order of
   preference: `rfl`; `by decide`; `by simp only [C, decBat_guardBody, ...]`.
   One of the first two will close them — they are structural equalities of
   closed terms. If `decide` is slow, that is acceptable; correctness over
   compile speed here.
3. **Port statements.** All `NockEval ... (atom n)` become
   `NockEval ... (.val (atom n))`. `callGate_gate_eval`'s hypothesis and
   conclusion both wrap in `.val` and generalize: state it with `o : Outcome`
   in tail position (hypothesis `NockEval (cell bat (cell arg ctx)) bat o`,
   conclusion `... o`) — this is a strict improvement and ports the proof
   unchanged (op9/op10 chains are outcome-polymorphic in tail position).
4. **Port proofs mechanically.** Old pattern
   `have h := @NockEval.op0 s (atom 6); simp [fas] at h` becomes
   `NockEval.op0 (by simp [decLoopCore, fasO])` or
   `NockEval.op0 (fasO_six ...)` where a named lemma fits. `rw [hax_six]`
   becomes supplying `haxO_six` as the `op10` equality hypothesis. `lus`
   rewrites become `lusO` equation hypotheses discharged by `rfl`/`simp
   [lusO]`. The `dec_loop_inv` induction structure is unchanged.
5. **The flagship new theorem** — this is the acceptance test of the entire
   refactor. The underflow case, previously provable-*wrong*, must now be
   provable-*crashing*:

```lean
theorem dec_underflow (ctx : Noun) :
    NockEval (cell decBat (cell (atom 0) ctx)) decBat .exit
```

Expected proof shape: `op11_dynamic` (hint computes, `.exit` passes through
tail position) → `op6_then` (guard test `=(0 sample)` evaluates to
`tisN (atom 0) (atom 0) = atom 0`, i.e. true) → then-branch is `[0 0]` →
`op0_crash rfl` (since `fasO (atom 0) _ = none`). The `.exit` propagates
outward through the tail-position `o` parameters with no extra constructors.

6. **`add`/`sub`:** port `AddCtx`/`SubCtx` and their theorems the same way.
   If the port stalls, `dec` end-to-end plus `dec_underflow` is the required
   deliverable; flag add/sub as incomplete rather than forcing them.

**Acceptance (Phase 3):** `dec_correct` (with `.val`) and `dec_underflow`
proved; `#print axioms dec_correct` shows no `Lean.ofReduceBool`;
`RuntimeBridge.lean` is the only file mentioning `native_decide`.

---

## 6. Phase 4 — DO NOT START

The composition-theorem development (free monoid of words, the `N`/`C`
compiler folds, the leaf-contract structures) is Phase 4 and requires design
review first. Do not scaffold it speculatively.

---

## 7. Pitfalls (read before writing code)

- **The `Inhabited`/`panic!` trap is the reason for this refactor.** Never
  use `.get!`, `.iget`, `Option.get!`, `panic!`, or `default` in any
  proof-facing definition. If you find yourself needing one, the design is
  being violated — stop.
- **`Noun` keeps `deriving Inhabited`** (the `partial def nock` evaluator
  needs it). That is fine; the invariant is that no proof-facing definition
  *consumes* it.
- **`simp [fasO]` unfolds one layer**; for deep axes prefer the named lemmas
  (`fasO_six`, etc.) exactly as the old proofs preferred `fas_six`.
- **`omega` over `ring`** — no Mathlib.
- **Constructor names are API.** Downstream work (the composition theorem,
  the paper's artifact) will reference them; do not rename during
  implementation.
- **Left-to-right strictness is semantic content**, not style. Adding a
  "right crashes first" constructor anywhere breaks determinism. The
  constructor list in §3 is exhaustive; implement exactly it.
- After each phase: `lake build && lake exec main`, and re-run the grep gates
  (`panic`, `sorry`, `native_decide` locations).

## 8. Definition of done

1. `lake build` clean on Lean 4.28.0, no `sorry`, no new axioms declared.
2. Grep gates: `panic` only in `partial def nock`; `native_decide` only in
   `Nock/RuntimeBridge.lean`.
3. Phase 1 sanity examples pass, including the two crash examples.
4. `nockF_sound`, `nockF_mono`, `nockF_complete`, `NockEval.deterministic`,
   `diverges_iff_fuel` proved.
5. `dec_correct` and `dec_underflow` proved; axiom footprint of both is
   `propext`/`Quot.sound` (+ `Classical.choice` tolerated).
6. README updated: crash-by-absence claim removed, replaced by the
   three-valued outcome description; axiom claims corrected to match
   `#print axioms` output.
