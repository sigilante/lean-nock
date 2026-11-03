import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.HoonOne
import Nock.Notation

namespace Nock
open Noun

/-!
# `++dec` on a cell diverges

Hoon's compiled `++dec` has a three-point ⊥ profile:

| input | outcome | theorem |
| --- | --- | --- |
| `atom (n+1)` | `.val (atom n)` | `dec_correct` (HoonOne) |
| `atom 0` | `.exit` | `dec_underflow` (HoonOne) |
| `cell _ _` | divergence | `dec_cell_diverges` (here) |

The zero-guard `?< =(0 a)` passes on a cell (a cell is not `atom 0`), and the
count-up loop's test `=(a +(b))` compares a cell against an atom, which is
`atom 1` forever.  So the loop takes its else branch at every iteration and
never terminates.

Divergence is the absence of a derivation, so the proof is a refutation: from
any `NockEval` derivation on this subject we derive `False`.  The engine is
`NockEval.deterministic` — at each layer we construct the *canonical*
derivation of the subformula and use determinism to prune every constructor
whose outcome disagrees.  That pattern appears about fifteen times below.
-/

-- ---------------------------------------------------------------------------
-- Determinism-pruning idiom
-- ---------------------------------------------------------------------------

/-- A formula cannot both return and crash on the same subject. -/
private theorem no_val_exit {s f v} (hv : NockEval s f (.val v))
    (he : NockEval s f .exit) : False := by
  have := NockEval.deterministic hv he; simp at this

/-- Two values derived for the same subject/formula agree. -/
private theorem det_val {s f} {u v : Noun} (h1 : NockEval s f (.val u))
    (h2 : NockEval s f (.val v)) : u = v := by
  have := NockEval.deterministic h1 h2; simpa using this

-- ---------------------------------------------------------------------------
-- Named pieces of decLoopBat
-- ---------------------------------------------------------------------------

/-- The loop test `=(a +(b))`: compares axis 30 (the sample) with `+(axis 6)`. -/
def decCondF : Noun :=
  cell (atom 5) (cell (cell (atom 0) (atom 30)) (cell (atom 4) (cell (atom 0) (atom 6))))

/-- The loop's then-branch: return the counter `b` at axis 6. -/
def decThenF : Noun := cell (atom 0) (atom 6)

/-- The op10 edit that bumps the counter: `#[6 +(/[6 core]) core]`. -/
def decEditF : Noun :=
  cell (atom 10) (cell (cell (atom 6) (cell (atom 4) (cell (atom 0) (atom 6))))
                       (cell (atom 0) (atom 1)))

/-- The loop's else-branch: bump the counter, then fire the battery again. -/
def decElseArm : Noun := cell (atom 9) (cell (atom 2) decEditF)

theorem decLoopBat_parts :
    decLoopBat = cell (atom 6) (cell decCondF (cell decThenF decElseArm)) := rfl

-- ---------------------------------------------------------------------------
-- Sample-generalized loop infrastructure
--
-- The existing helpers are parametric in `n : Nat`.  The edit and the slot
-- lookups never inspect the sample, so these generalizations have the same
-- proofs.  Nothing in HoonOne is modified.
-- ---------------------------------------------------------------------------

/-- Loop core with an arbitrary noun in the sample slot (axis 30). -/
def decLoopCoreG (b : Nat) (sam ctx : Noun) : Noun :=
  cell decLoopBat (cell (atom b) (cell decBat (cell sam ctx)))

theorem decLoopCoreG_atom (b n : Nat) (ctx : Noun) :
    decLoopCoreG b (atom n) ctx = decLoopCore b n ctx := rfl

private theorem dec_slot6_evalG (b : Nat) (sam ctx : Noun) :
    NockEval (decLoopCoreG b sam ctx) (cell (atom 0) (atom 6)) (.val (atom b)) :=
  NockEval.op0 (by simp [decLoopCoreG, fasO])

private theorem dec_cond_evalG (b : Nat) (sam ctx : Noun) :
    NockEval (decLoopCoreG b sam ctx) decCondF (.val (tisN sam (atom (1 + b)))) :=
  NockEval.op5
    (NockEval.op0 (by simp [decLoopCoreG, fasO]))
    (NockEval.op4 (dec_slot6_evalG b sam ctx) (lusO_atom b))

private theorem dec_edit_coreG (b : Nat) (sam ctx : Noun) :
    NockEval (decLoopCoreG b sam ctx) decEditF (.val (decLoopCoreG (b + 1) sam ctx)) := by
  refine NockEval.op10
    (NockEval.op0 (fasO_one _))
    (NockEval.op4 (dec_slot6_evalG b sam ctx) (lusO_atom b)) ?_
  show haxO (atom 6) (atom (1 + b)) (decLoopCoreG b sam ctx)
    = some (decLoopCoreG (b + 1) sam ctx)
  simp [decLoopCoreG, haxO_six, Nat.add_comm]

/-- Firing the battery from a loop core looks up `decLoopBat` at axis 2. -/
private theorem fasO_two_loopCoreG (b : Nat) (sam ctx : Noun) :
    fasO (atom 2) (decLoopCoreG b sam ctx) = some decLoopBat :=
  fasO_head _ _

-- ---------------------------------------------------------------------------
-- The loop lemma
-- ---------------------------------------------------------------------------

/-!
## Correction to SPEC-PHASE4 §1.3

This lemma departs from the recipe in **SPEC-PHASE4 §1.3**, which **§4** lists
as a load-bearing pitfall ("the §1.3 index-generalization phrasing is
load-bearing; do not 'simplify' the aux lemma to concrete indices").  The
departure is the opposite of simplifying: §1.3 generalizes too *little*, and as
written it cannot close.

§1.3 fixes `f = decLoopBat`, generalizes only the counter, and then says that
in the `op6_else` case one should `cases` the else-branch sub-derivation and,
in its `op9` case, "apply the induction hypothesis with `b + 1`".  **There is
no such induction hypothesis.**  Structural induction on an indexed derivation
yields an IH only for *immediate* sub-derivations.  The IH available in
`op6_else` is the one for the else-branch, whose formula index is `decElseArm`
rather than `decLoopBat`; with `f` fixed it is unusable.  The derivation that
does return to `decLoopBat` sits one layer deeper, inside that branch's `op9`,
and `cases` on the else-branch discards any IH for it.

The fix keeps §1.3's intent — index generalization — and widens it.  The
statement is generalized over the counter *and* over the formula, which ranges
over the two-element set `{decLoopBat, decElseArm}`.  Then:

* `op6_else` closes by its own IH at `Or.inr rfl`;
* `op9` closes the recursion by its IH at `b + 1`, `Or.inl rfl`.

The counter must still be universally quantified, because each iteration
reaches the loop battery at `b + 1` rather than `b`.

SPEC-PHASE4 §1.4's *statements* (`dec_loop_cell_diverges`, `dec_cell_diverges`)
are unchanged; only this private aux lemma moved.

The equalities are taken as *hypotheses* rather than substituted, so that the
indices stay variables and the motive is accepted.  That half of §1.3's
pitfall note is correct, and is followed here.
-/
private theorem dec_loop_cell_aux (x y ctx : Noun) :
    ∀ {s f : Noun} {o : Outcome}, NockEval s f o →
      ∀ k : Nat, s = decLoopCoreG k (cell x y) ctx →
        (f = decLoopBat ∨ f = decElseArm) → False := by
  intro s f o h
  induction h with
  | @crash_malformed a ff hm =>
    intro _ _ hf
    rcases hf with rfl | rfl <;> exact absurd hm (by decide)
  -- the loop battery: [6 cond then else]
  | @op6_then a bb c d oo h1 _ _ _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp only [decLoopBat_parts, Noun.cell.injEq] at hf
      obtain ⟨-, hb, -, -⟩ := hf
      subst hb; subst hs
      have canon := dec_cond_evalG k (cell x y) ctx
      rw [tisN_cell_atom] at canon
      have := NockEval.deterministic h1 canon; simp at this
    · simp [decElseArm] at hf
  | @op6_else a bb c d oo _ _ _ ih2 =>
    intro k hs hf
    rcases hf with hf | hf
    · simp only [decLoopBat_parts, Noun.cell.injEq] at hf
      obtain ⟨-, -, -, hd⟩ := hf
      subst hd
      exact ih2 k hs (Or.inr rfl)
    · simp [decElseArm] at hf
  | @op6_nonloob a bb c d r h1 _ hne1 _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp only [decLoopBat_parts, Noun.cell.injEq] at hf
      obtain ⟨-, hb, -, -⟩ := hf
      subst hb; subst hs
      have canon := dec_cond_evalG k (cell x y) ctx
      rw [tisN_cell_atom] at canon
      exact hne1 (det_val h1 canon)
    · simp [decElseArm] at hf
  | @op6_crash a bb c d h1 _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp only [decLoopBat_parts, Noun.cell.injEq] at hf
      obtain ⟨-, hb, -, -⟩ := hf
      subst hb; subst hs
      have canon := dec_cond_evalG k (cell x y) ctx
      rw [tisN_cell_atom] at canon
      exact no_val_exit canon h1
    · simp [decElseArm] at hf
  -- the else-arm: [9 2 edit]
  | @op9 a bax c core arm oo h1 h2 _ _ ih3 =>
    intro k hs hf
    rcases hf with hf | hf
    · simp [decLoopBat_parts] at hf
    · simp only [decElseArm, Noun.cell.injEq] at hf
      obtain ⟨-, hbax, hc⟩ := hf
      subst hbax; subst hc; subst hs
      have hcore : core = decLoopCoreG (k + 1) (cell x y) ctx :=
        det_val h1 (dec_edit_coreG k (cell x y) ctx)
      subst hcore
      rw [fasO_two_loopCoreG] at h2
      have harm : arm = decLoopBat := by simpa using h2.symm
      subst harm
      exact ih3 (k + 1) rfl (Or.inl rfl)
  | @op9_badaxis a bax c core h1 h2 _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp [decLoopBat_parts] at hf
    · simp only [decElseArm, Noun.cell.injEq] at hf
      obtain ⟨-, hbax, hc⟩ := hf
      subst hbax; subst hc; subst hs
      have hcore : core = decLoopCoreG (k + 1) (cell x y) ctx :=
        det_val h1 (dec_edit_coreG k (cell x y) ctx)
      subst hcore
      rw [fasO_two_loopCoreG] at h2
      simp at h2
  | @op9_crash a bax c h1 _ =>
    intro k hs hf
    rcases hf with hf | hf
    · simp [decLoopBat_parts] at hf
    · simp only [decElseArm, Noun.cell.injEq] at hf
      obtain ⟨-, -, hc⟩ := hf
      subst hc; subst hs
      exact no_val_exit (dec_edit_coreG k (cell x y) ctx) h1
  -- every other constructor's formula head disagrees with both targets
  | _ =>
    intro _ _ hf
    rcases hf with hf | hf <;> simp [decLoopBat_parts, decElseArm] at hf

/-- The `++dec` count-up loop, started from any counter, never terminates when
    the sample is a cell. -/
theorem dec_loop_cell_diverges (b : Nat) (x y ctx : Noun) :
    Diverges (decLoopCoreG b (cell x y) ctx) decLoopBat :=
  fun _ h => dec_loop_cell_aux x y ctx h b rfl (Or.inl rfl)

-- ---------------------------------------------------------------------------
-- The gate-level theorem
-- ---------------------------------------------------------------------------

/-- **`++dec` on a cell diverges.**  With a cell sample the zero-guard passes
    (a cell is not `atom 0`), the loop is entered, and its test is `atom 1`
    forever.  No `NockEval` derivation exists — neither a value nor a crash.

    Together with `dec_correct` and `dec_underflow` this completes the ⊥
    profile of Hoon's compiled `++dec`. -/
theorem dec_cell_diverges (x y ctx : Noun) :
    Diverges (cell decBat (cell (cell x y) ctx)) decBat := by
  intro o h
  -- decBat unfolds definitionally to its op11 hint layer
  have hS : NockEval (cell decBat (cell (cell x y) ctx))
      (cell (atom 11) (cell (cell (atom 1851876717) decBat_hintF) decBat_guardBody)) o := h
  clear h
  -- The canonical guard test: =(0 sample) with a cell sample is `atom 1`.
  have htest : NockEval (cell decBat (cell (cell x y) ctx))
      (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 6))))
      (.val (atom 1)) := by
    have h0 : NockEval (cell decBat (cell (cell x y) ctx))
        (cell (atom 1) (atom 0)) (.val (atom 0)) := NockEval.op1
    have h6 : NockEval (cell decBat (cell (cell x y) ctx))
        (cell (atom 0) (atom 6)) (.val (cell x y)) := NockEval.op0 (by simp [fasO])
    have hq := NockEval.op5 h0 h6
    rwa [tisN_atom_cell] at hq
  -- Layer 1: the `~_` hint.  Its clue computes, so op11_dyn_crash is impossible.
  cases hS with
  | crash_malformed hm => exact absurd hm (by decide)
  | op11_dyn_crash hc =>
    obtain ⟨_, hr⟩ := dec_hint_eval (cell decBat (cell (cell x y) ctx))
    exact no_val_exit hr hc
  | op11_dynamic _ hbody =>
    -- Layer 2: the underflow guard.  Test is `atom 1`, so only op6_else survives.
    rw [guardBody_parts] at hbody
    cases hbody with
    | crash_malformed hm => exact absurd hm (by decide)
    | op6_then ht _ => have := NockEval.deterministic ht htest; simp at this
    | op6_nonloob ht _ hne1 => exact hne1 (det_val ht htest)
    | op6_crash ht => exact no_val_exit htest ht
    | op6_else _ helse =>
      -- Layer 3: two op8 pushes (b := 0, then the loop battery).
      rw [pushLoop_parts] at helse
      cases helse with
      | crash_malformed hm => exact absurd hm (by decide)
      | op8_crash hb =>
        exact no_val_exit
          (show NockEval _ (cell (atom 1) (atom 0)) (.val (atom 0)) from NockEval.op1) hb
      | @op8 _ _ _ r1 _ hb hrest =>
        have hr1 : r1 = atom 0 :=
          det_val hb (show NockEval _ (cell (atom 1) (atom 0)) (.val (atom 0)) from NockEval.op1)
        subst hr1
        cases hrest with
        | crash_malformed hm => exact absurd hm (by decide)
        | op8_crash hb2 =>
          exact no_val_exit
            (show NockEval _ (cell (atom 1) decLoopBat) (.val decLoopBat) from NockEval.op1) hb2
        | @op8 _ _ _ r2 _ hb2 hfire =>
          have hr2 : r2 = decLoopBat :=
            det_val hb2
              (show NockEval _ (cell (atom 1) decLoopBat) (.val decLoopBat) from NockEval.op1)
          subst hr2
          -- The subject is now `decLoopCoreG 0 (cell x y) ctx`, definitionally.
          have hfire' : NockEval (decLoopCoreG 0 (cell x y) ctx)
              (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))) o := hfire
          -- Layer 4: fire the battery, landing in the divergent loop.
          cases hfire' with
          | crash_malformed hm => exact absurd hm (by decide)
          | op9_crash hc => exact no_val_exit (NockEval.op0 (fasO_one _)) hc
          | @op9_badaxis _ _ _ core hc hnone =>
            have hcore : core = decLoopCoreG 0 (cell x y) ctx :=
              det_val hc (NockEval.op0 (fasO_one _))
            subst hcore
            rw [fasO_two_loopCoreG] at hnone
            simp at hnone
          | @op9 _ _ _ core arm _ hc harm hloop =>
            have hcore : core = decLoopCoreG 0 (cell x y) ctx :=
              det_val hc (NockEval.op0 (fasO_one _))
            subst hcore
            rw [fasO_two_loopCoreG] at harm
            have harm' : arm = decLoopBat := by simpa using harm.symm
            subst harm'
            exact dec_loop_cell_diverges 0 x y ctx o hloop

end Nock
