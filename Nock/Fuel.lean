import Nock.Basic
import Nock.Proofs
import Nock.Eval
open Noun

/-!
# Fuel interpreter for Nock 4K

`nockF k a f` runs `f` against `a` for at most `k` steps.

    none            fuel exhausted — no verdict yet
    some (.val n)   returned the noun `n`
    some .exit      crashed, deterministically

This is the computational counterpart of the `NockEval` relation.  It exists
to make three things provable that the relation alone cannot express:

* `nockF_sound` / `nockF_complete` — the interpreter and the relation agree;
* `NockEval.deterministic` — a corollary of the above, obtained by running
  both derivations through the *function* `nockF` at a common fuel;
* `diverges_iff_fuel` — divergence, which is the *absence* of a `NockEval`
  derivation, is equivalently "`nockF` returns `none` at every fuel".

The match tree below follows the constructor list of `NockEval` line for
line, and every recursive call decrements the fuel.  The nested `match`es on
recursive results are deliberately explicit rather than monadic: soundness is
proved by an induction that mirrors this syntax, and a `>>=` would bury the
crash-propagation cases the proof needs to see.
-/

def nockF : Nat → Noun → Noun → Option Outcome
  | 0, _, _ => none
  -- a bare atom is not a formula
  | _ + 1, _, atom _ => some .exit
  -- *[a [b c] d] = [*[a b c] *[a d]]
  | fuel + 1, a, cell (cell b c) fol =>
      match nockF fuel a (cell b c) with
      | none            => none
      | some .exit      => some .exit
      | some (.val r1)  =>
        match nockF fuel a fol with
        | none           => none
        | some .exit     => some .exit
        | some (.val r2) => some (.val (cell r1 r2))
  | fuel + 1, a, cell (atom k) t =>
    match k, t with
    -- *[a 0 b] = /[b a]
    | 0, fol =>
      match fasO fol a with
      | some r => some (.val r)
      | none   => some .exit
    -- *[a 1 b] = b
    | 1, fol => some (.val fol)
    -- *[a 2 b c] = *[*[a b] *[a c]]
    | 2, cell b c =>
      match nockF fuel a b with
      | none           => none
      | some .exit     => some .exit
      | some (.val r1) =>
        match nockF fuel a c with
        | none           => none
        | some .exit     => some .exit
        | some (.val r2) => nockF fuel r1 r2
    | 2, _ => some .exit
    -- *[a 3 b] = ?*[a b]
    | 3, fol =>
      match nockF fuel a fol with
      | none          => none
      | some .exit    => some .exit
      | some (.val r) => some (.val (wut r))
    -- *[a 4 b] = +*[a b]
    | 4, fol =>
      match nockF fuel a fol with
      | none          => none
      | some .exit    => some .exit
      | some (.val r) =>
        match lusO r with
        | some v => some (.val v)
        | none   => some .exit
    -- *[a 5 b c] = =[*[a b] *[a c]]
    | 5, cell b c =>
      match nockF fuel a b with
      | none           => none
      | some .exit     => some .exit
      | some (.val r1) =>
        match nockF fuel a c with
        | none           => none
        | some .exit     => some .exit
        | some (.val r2) => some (.val (tisN r1 r2))
    | 5, _ => some .exit
    -- *[a 6 b c d]: semantic if-then-else, crash on non-loobean test
    | 6, cell b (cell c d) =>
      match nockF fuel a b with
      | none                  => none
      | some .exit            => some .exit
      | some (.val (atom 0))  => nockF fuel a c
      | some (.val (atom 1))  => nockF fuel a d
      | some (.val _)         => some .exit
    | 6, _ => some .exit
    -- *[a 7 b c] = *[*[a b] c]
    | 7, cell b c =>
      match nockF fuel a b with
      | none           => none
      | some .exit     => some .exit
      | some (.val r1) => nockF fuel r1 c
    | 7, _ => some .exit
    -- *[a 8 b c] = *[[*[a b] a] c]
    | 8, cell b c =>
      match nockF fuel a b with
      | none           => none
      | some .exit     => some .exit
      | some (.val r1) => nockF fuel (cell r1 a) c
    | 8, _ => some .exit
    -- *[a 9 b c] = *[core /[b core]]
    | 9, cell b c =>
      match nockF fuel a c with
      | none             => none
      | some .exit       => some .exit
      | some (.val core) =>
        match fasO b core with
        | some arm => nockF fuel core arm
        | none     => some .exit
    | 9, _ => some .exit
    -- *[a 10 [b c] d] = #[b *[a c] *[a d]]
    | 10, cell (cell b c) d =>
      match nockF fuel a c with
      | none           => none
      | some .exit     => some .exit
      | some (.val r1) =>
        match nockF fuel a d with
        | none           => none
        | some .exit     => some .exit
        | some (.val r2) =>
          match haxO b r1 r2 with
          | some v => some (.val v)
          | none   => some .exit
    | 10, _ => some .exit
    -- *[a 11 t c] = *[a c]        (static hint)
    | 11, cell (atom _) c => nockF fuel a c
    -- *[a 11 [t c] d] = *[a d]    (dynamic hint)
    | 11, cell (cell _ c) d =>
      match nockF fuel a c with
      | none          => none
      | some .exit    => some .exit
      | some (.val _) => nockF fuel a d
    | 11, _ => some .exit
    -- opcode ≥ 12
    | _, _ => some .exit

-- ---------------------------------------------------------------------------
-- Soundness: every verdict the interpreter reaches is a real derivation.
-- ---------------------------------------------------------------------------

theorem nockF_sound : ∀ (k : Nat) {a f o}, nockF k a f = some o → NockEval a f o := by
  intro k
  induction k with
  | zero => intro a f o h; simp [nockF] at h
  | succ k ih =>
    intro a f o h
    match f, h with
    -- atom formula
    | atom _, h =>
      simp only [nockF, Option.some.injEq] at h; subst h
      exact .crash_malformed rfl
    -- autocons
    | cell (cell b c) fol, h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .autocons_crashL (ih h1)
      next r1 h1 =>
        split at h
        next h2 => simp at h
        next h2 =>
          simp only [Option.some.injEq] at h; subst h
          exact .autocons_crashR (ih h1) (ih h2)
        next r2 h2 =>
          simp only [Option.some.injEq] at h; subst h
          exact .autocons (ih h1) (ih h2)
    -- op 0
    | cell (atom 0) fol, h =>
      simp only [nockF] at h
      split at h
      next r hr => simp only [Option.some.injEq] at h; subst h; exact .op0 hr
      next hr => simp only [Option.some.injEq] at h; subst h; exact .op0_crash hr
    -- op 1
    | cell (atom 1) fol, h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .op1
    -- op 2
    | cell (atom 2) (atom _), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 2) (cell b c), h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op2_crashL (ih h1)
      next r1 h1 =>
        split at h
        next h2 => simp at h
        next h2 =>
          simp only [Option.some.injEq] at h; subst h
          exact .op2_crashR (ih h1) (ih h2)
        next r2 h2 => exact .op2 (ih h1) (ih h2) (ih h)
    -- op 3
    | cell (atom 3) fol, h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op3_crash (ih h1)
      next r h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op3 (ih h1)
    -- op 4
    | cell (atom 4) fol, h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op4_crash (ih h1)
      next r h1 =>
        split at h
        next v hv => simp only [Option.some.injEq] at h; subst h; exact .op4 (ih h1) hv
        next hv => simp only [Option.some.injEq] at h; subst h; exact .op4_cell (ih h1) hv
    -- op 5
    | cell (atom 5) (atom _), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 5) (cell b c), h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op5_crashL (ih h1)
      next r1 h1 =>
        split at h
        next h2 => simp at h
        next h2 =>
          simp only [Option.some.injEq] at h; subst h
          exact .op5_crashR (ih h1) (ih h2)
        next r2 h2 =>
          simp only [Option.some.injEq] at h; subst h
          exact .op5 (ih h1) (ih h2)
    -- op 6
    | cell (atom 6) (atom _), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 6) (cell b (atom _)), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 6) (cell b (cell c d)), h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op6_crash (ih h1)
      next h1 => exact .op6_then (ih h1) (ih h)
      next h1 => exact .op6_else (ih h1) (ih h)
      next r hne0 hne1 h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op6_nonloob (ih h1) hne0 hne1
    -- op 7
    | cell (atom 7) (atom _), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 7) (cell b c), h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op7_crash (ih h1)
      next r1 h1 => exact .op7 (ih h1) (ih h)
    -- op 8
    | cell (atom 8) (atom _), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 8) (cell b c), h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op8_crash (ih h1)
      next r1 h1 => exact .op8 (ih h1) (ih h)
    -- op 9
    | cell (atom 9) (atom _), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 9) (cell b c), h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op9_crash (ih h1)
      next core h1 =>
        split at h
        next arm harm => exact .op9 (ih h1) harm (ih h)
        next harm =>
          simp only [Option.some.injEq] at h; subst h
          exact .op9_badaxis (ih h1) harm
    -- op 10
    | cell (atom 10) (atom _), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 10) (cell (atom _) _), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 10) (cell (cell b c) d), h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op10_crashL (ih h1)
      next r1 h1 =>
        split at h
        next h2 => simp at h
        next h2 =>
          simp only [Option.some.injEq] at h; subst h
          exact .op10_crashR (ih h1) (ih h2)
        next r2 h2 =>
          split at h
          next v hv => simp only [Option.some.injEq] at h; subst h; exact .op10 (ih h1) (ih h2) hv
          next hv =>
            simp only [Option.some.injEq] at h; subst h
            exact .op10_badaxis (ih h1) (ih h2) hv
    -- op 11
    | cell (atom 11) (atom _), h =>
      simp only [nockF, Option.some.injEq] at h; subst h; exact .crash_malformed rfl
    | cell (atom 11) (cell (atom t) c), h =>
      simp only [nockF] at h
      exact .op11_static (ih h)
    | cell (atom 11) (cell (cell t c) d), h =>
      simp only [nockF] at h
      split at h
      next h1 => simp at h
      next h1 =>
        simp only [Option.some.injEq] at h; subst h
        exact .op11_dyn_crash (ih h1)
      next r1 h1 => exact .op11_dynamic (ih h1) (ih h)
    -- opcode ≥ 12
    | cell (atom (n + 12)) t, h =>
      simp only [nockF, Option.some.injEq] at h; subst h
      exact .crash_malformed rfl

-- ---------------------------------------------------------------------------
-- Monotonicity: more fuel never changes or retracts a verdict.
-- ---------------------------------------------------------------------------

theorem nockF_mono : ∀ {k k' a f o}, nockF k a f = some o → k ≤ k' → nockF k' a f = some o := by
  intro k
  induction k with
  | zero => intro k' a f o h _; simp [nockF] at h
  | succ k ih =>
    intro k' a f o h hk
    obtain ⟨m, rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by omega⟩
    have hkm : k ≤ m := by omega
    match f, h with
    | atom _, h => simp only [nockF] at h ⊢; exact h
    -- autocons
    | cell (cell b c) fol, h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next r1 h1 =>
        rw [ih h1 hkm]
        split at h
        next h2 => simp at h
        next h2 => rw [ih h2 hkm]; exact h
        next r2 h2 => rw [ih h2 hkm]; exact h
    | cell (atom 0) fol, h => simp only [nockF] at h ⊢; exact h
    | cell (atom 1) fol, h => simp only [nockF] at h ⊢; exact h
    | cell (atom 2) (atom _), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 2) (cell b c), h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next r1 h1 =>
        rw [ih h1 hkm]
        split at h
        next h2 => simp at h
        next h2 => rw [ih h2 hkm]; exact h
        next r2 h2 => rw [ih h2 hkm]; exact ih h hkm
    | cell (atom 3) fol, h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next r h1 => rw [ih h1 hkm]; exact h
    | cell (atom 4) fol, h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next r h1 => rw [ih h1 hkm]; exact h
    | cell (atom 5) (atom _), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 5) (cell b c), h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next r1 h1 =>
        rw [ih h1 hkm]
        split at h
        next h2 => simp at h
        next h2 => rw [ih h2 hkm]; exact h
        next r2 h2 => rw [ih h2 hkm]; exact h
    | cell (atom 6) (atom _), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 6) (cell b (atom _)), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 6) (cell b (cell c d)), h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next h1 => rw [ih h1 hkm]; exact ih h hkm
      next h1 => rw [ih h1 hkm]; exact ih h hkm
      next r hne0 hne1 h1 =>
        -- the test is non-loobean; case on `r` so the match reduces concretely
        have hr : nockF m a b = some (.val r) := ih h1 hkm
        match r, hne0, hne1, hr with
        | atom 0, hne0, _, _ => exact absurd rfl hne0
        | atom 1, _, hne1, _ => exact absurd rfl hne1
        | atom (_ + 2), _, _, hr => simp only [hr]; exact h
        | cell _ _, _, _, hr => simp only [hr]; exact h
    | cell (atom 7) (atom _), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 7) (cell b c), h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next r1 h1 => rw [ih h1 hkm]; exact ih h hkm
    | cell (atom 8) (atom _), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 8) (cell b c), h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next r1 h1 => rw [ih h1 hkm]; exact ih h hkm
    | cell (atom 9) (atom _), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 9) (cell b c), h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next core h1 =>
        have hc : nockF m a c = some (.val core) := ih h1 hkm
        split at h
        next arm harm => simp only [hc, harm]; exact ih h hkm
        next harm => simp only [hc, harm]; exact h
    | cell (atom 10) (atom _), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 10) (cell (atom _) _), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 10) (cell (cell b c) d), h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next r1 h1 =>
        rw [ih h1 hkm]
        split at h
        next h2 => simp at h
        next h2 => rw [ih h2 hkm]; exact h
        next r2 h2 => rw [ih h2 hkm]; exact h
    | cell (atom 11) (atom _), h => simp only [nockF] at h ⊢; exact h
    | cell (atom 11) (cell (atom t) c), h =>
      simp only [nockF] at h ⊢; exact ih h hkm
    | cell (atom 11) (cell (cell t c) d), h =>
      simp only [nockF] at h ⊢
      split at h
      next h1 => simp at h
      next h1 => rw [ih h1 hkm]; exact h
      next r1 h1 => rw [ih h1 hkm]; exact ih h hkm
    | cell (atom (n + 12)) t, h => simp only [nockF] at h ⊢; exact h

-- ---------------------------------------------------------------------------
-- Completeness: every derivation is reached by the interpreter at some fuel.
-- ---------------------------------------------------------------------------

/-- A malformed formula crashes at any nonzero fuel. -/
theorem nockF_malformed : ∀ {k a f}, Malformed f = true → nockF (k + 1) a f = some .exit := by
  intro k a f h
  match f with
  | atom _ => rfl
  | cell (cell _ _) _ => simp [Malformed] at h
  | cell (atom 0) _ => simp [Malformed] at h
  | cell (atom 1) _ => simp [Malformed] at h
  | cell (atom 2) (atom _) => rfl
  | cell (atom 2) (cell _ _) => simp [Malformed] at h
  | cell (atom 3) _ => simp [Malformed] at h
  | cell (atom 4) _ => simp [Malformed] at h
  | cell (atom 5) (atom _) => rfl
  | cell (atom 5) (cell _ _) => simp [Malformed] at h
  | cell (atom 6) (atom _) => rfl
  | cell (atom 6) (cell _ (atom _)) => rfl
  | cell (atom 6) (cell _ (cell _ _)) => simp [Malformed] at h
  | cell (atom 7) (atom _) => rfl
  | cell (atom 7) (cell _ _) => simp [Malformed] at h
  | cell (atom 8) (atom _) => rfl
  | cell (atom 8) (cell _ _) => simp [Malformed] at h
  | cell (atom 9) (atom _) => rfl
  | cell (atom 9) (cell _ _) => simp [Malformed] at h
  | cell (atom 10) (atom _) => rfl
  | cell (atom 10) (cell (atom _) _) => rfl
  | cell (atom 10) (cell (cell _ _) _) => simp [Malformed] at h
  | cell (atom 11) (atom _) => rfl
  | cell (atom 11) (cell (atom _) _) => simp [Malformed] at h
  | cell (atom 11) (cell (cell _ _) _) => simp [Malformed] at h
  | cell (atom (_ + 12)) _ => rfl

theorem nockF_complete {a f o} (h : NockEval a f o) : ∃ k, nockF k a f = some o := by
  induction h with
  | crash_malformed hm => exact ⟨1, nockF_malformed hm⟩
  -- autocons
  | autocons _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  | autocons_crashL _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1
    exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  | autocons_crashR _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  -- op 0 / 1
  | op0 hf => exact ⟨1, by simp only [nockF, hf]⟩
  | op0_crash hf => exact ⟨1, by simp only [nockF, hf]⟩
  | op1 => exact ⟨1, rfl⟩
  -- op 2
  | op2 _ _ _ ih1 ih2 ih3 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2; obtain ⟨k3, hk3⟩ := ih3
    have e1 := nockF_mono hk1 (show k1 ≤ max (max k1 k2) k3 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max (max k1 k2) k3 by omega)
    have e3 := nockF_mono hk3 (show k3 ≤ max (max k1 k2) k3 by omega)
    exact ⟨max (max k1 k2) k3 + 1, by simp only [nockF, e1, e2, e3]⟩
  | op2_crashL _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1
    exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  | op2_crashR _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  -- op 3
  | op3 _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  | op3_crash _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  -- op 4
  | op4 _ hl ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1, hl]⟩
  | op4_cell _ hl ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1, hl]⟩
  | op4_crash _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  -- op 5
  | op5 _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  | op5_crashL _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  | op5_crashR _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  -- op 6
  | op6_then _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  | op6_else _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  | @op6_nonloob a b c d r _ hne0 hne1 ih1 =>
    obtain ⟨k1, hk1⟩ := ih1
    refine ⟨k1 + 1, ?_⟩
    match r, hne0, hne1, hk1 with
    | atom 0, hne0, _, _ => exact absurd rfl hne0
    | atom 1, _, hne1, _ => exact absurd rfl hne1
    | atom (_ + 2), _, _, hk1 => simp only [nockF, hk1]
    | cell _ _, _, _, hk1 => simp only [nockF, hk1]
  | op6_crash _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  -- op 7
  | op7 _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  | op7_crash _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  -- op 8
  | op8 _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  | op8_crash _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  -- op 9
  | op9 _ harm _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, harm, e2]⟩
  | op9_badaxis _ harm ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1, harm]⟩
  | op9_crash _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  -- op 10
  | op10 _ _ hv ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2, hv]⟩
  | op10_badaxis _ _ hv ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2, hv]⟩
  | op10_crashL _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩
  | op10_crashR _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  -- op 11
  | op11_static _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF]; exact hk1⟩
  | op11_dynamic _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1; obtain ⟨k2, hk2⟩ := ih2
    have e1 := nockF_mono hk1 (show k1 ≤ max k1 k2 by omega)
    have e2 := nockF_mono hk2 (show k2 ≤ max k1 k2 by omega)
    exact ⟨max k1 k2 + 1, by simp only [nockF, e1, e2]⟩
  | op11_dyn_crash _ ih1 =>
    obtain ⟨k1, hk1⟩ := ih1; exact ⟨k1 + 1, by simp only [nockF, hk1]⟩

-- ---------------------------------------------------------------------------
-- Determinism, as a corollary via the interpreter.
-- ---------------------------------------------------------------------------

/-- Nock is deterministic: a subject and formula admit at most one outcome.

    Note the route.  Rather than a double induction on the two derivations
    with constructor-disjointness case analysis, we push both through the
    *function* `nockF` at a common fuel.  A function has one value, so the
    two outcomes coincide.  Left-to-right strictness in the crash-propagation
    constructors is what makes this true: a "right crashes first" variant
    anywhere would give `[0 0]`-style formulas two derivations. -/
theorem NockEval.deterministic {a f o₁ o₂}
    (h₁ : NockEval a f o₁) (h₂ : NockEval a f o₂) : o₁ = o₂ := by
  obtain ⟨k₁, hk₁⟩ := nockF_complete h₁
  obtain ⟨k₂, hk₂⟩ := nockF_complete h₂
  have e₁ := nockF_mono hk₁ (Nat.le_max_left  k₁ k₂)
  have e₂ := nockF_mono hk₂ (Nat.le_max_right k₁ k₂)
  simp [e₁] at e₂; exact e₂

-- ---------------------------------------------------------------------------
-- Divergence
-- ---------------------------------------------------------------------------

/-- `f` diverges on `a` when no outcome is derivable: it neither returns
    nor crashes.  This is the third value of the three-valued semantics,
    represented by the absence of a derivation rather than a constructor. -/
def Diverges (a f : Noun) : Prop := ∀ o, ¬ NockEval a f o

/-- Divergence is exactly "the interpreter never reaches a verdict".
    This is what makes divergence *statable*: `Diverges` quantifies over
    derivations, but the right-hand side is a decidable check at each fuel. -/
theorem diverges_iff_fuel (a f : Noun) :
    Diverges a f ↔ ∀ k, nockF k a f = none := by
  constructor
  · intro hdiv k
    match hk : nockF k a f with
    | none   => rfl
    | some o => exact absurd (nockF_sound k hk) (hdiv o)
  · intro hnone o hev
    obtain ⟨k, hk⟩ := nockF_complete hev
    rw [hnone k] at hk
    simp at hk
