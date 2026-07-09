import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.Comp
import Nock.Term
import Nock.CEval
open Noun

/-!
# Backward simulation: `NockEval → CEval`

Per SPEC-PHASE4B-PROOFS §0/§4: **do not induct on the `NockEval` derivation.**
`NockEval` is `Prop`-valued, so no height measure exists, and the nested
inversion depth would reproduce the SPEC-PHASE4 §1.3 trap exactly.

Instead convert the derivation to fuel with `nockF_complete` and induct on the
fuel, which measures *every* nested recursion uniformly.  Phase 2's interpreter
was built as a determinism-corollary machine; here it becomes the induction
measure for the simulation.

`nockF` is proof-chain-legal — the quarantine governs `CsemF`, the C-side
oracle, not `nockF`.
-/

-- ---------------------------------------------------------------------------
-- One-layer unfolding lemmas for `nockF`.  All `rfl`: `nockF` is structural on
-- the fuel, so each layer reduces definitionally once the formula head is
-- concrete.  (`fasO` never reduces by `rfl`; that is why the slot lookups stay
-- as `match fasO …` and get discharged by the named lemmas.)
-- ---------------------------------------------------------------------------

private theorem nF_op0 (k : Nat) (S fol : Noun) :
    nockF (k+1) S (cell (atom 0) fol) =
      (match fasO fol S with | some r => some (.val r) | none => some .exit) := rfl

private theorem nF_op7 (k : Nat) (S f g : Noun) :
    nockF (k+1) S (cell (atom 7) (cell f g)) =
      (match nockF k S f with
       | none => none | some .exit => some .exit
       | some (.val r) => nockF k r g) := rfl

private theorem nF_op8 (k : Nat) (S f g : Noun) :
    nockF (k+1) S (cell (atom 8) (cell f g)) =
      (match nockF k S f with
       | none => none | some .exit => some .exit
       | some (.val r) => nockF k (cell r S) g) := rfl

private theorem nF_op9 (k : Nat) (S bx c : Noun) :
    nockF (k+1) S (cell (atom 9) (cell bx c)) =
      (match nockF k S c with
       | none => none | some .exit => some .exit
       | some (.val core) =>
         match fasO bx core with
         | some arm => nockF k core arm
         | none => some .exit) := rfl

private theorem nF_op6 (k : Nat) (S b c d : Noun) :
    nockF (k+1) S (cell (atom 6) (cell b (cell c d))) =
      (match nockF k S b with
       | none => none | some .exit => some .exit
       | some (.val (atom 0)) => nockF k S c
       | some (.val (atom 1)) => nockF k S d
       | some (.val _) => some .exit) := rfl

private theorem nF_autocons (k : Nat) (S b c fol : Noun) :
    nockF (k+1) S (cell (cell b c) fol) =
      (match nockF k S (cell b c) with
       | none => none | some .exit => some .exit
       | some (.val r1) =>
         match nockF k S fol with
         | none => none | some .exit => some .exit
         | some (.val r2) => some (.val (cell r1 r2))) := rfl

-- Schema spines, kept abstract in the subject so `rw` matches without
-- unfolding `Lwhile` inside the subject `[L S]`.

private theorem nF_NT_seq (k : Nat) (S : Noun) (w : Word) (p : Term) :
    nockF (k+1) S (NT (.seq w p)) =
      (match nockF k S (phi w) with
       | none => none | some .exit => some .exit
       | some (.val r) => nockF k r (NT p)) := rfl

private theorem nF_NT_ifte (k : Nat) (S : Noun) (q₁ q₂ p : Term) :
    nockF (k+1) S (NT (.ifte q₁ q₂ p)) =
      (match nockF k S (Nifte q₁ q₂) with
       | none => none | some .exit => some .exit
       | some (.val r) => nockF k r (NT p)) := rfl

private theorem nF_NT_while (k : Nat) (S : Noun) (t b p : Term) :
    nockF (k+1) S (NT (.while t b p)) =
      (match nockF k S (Nwhile t b) with
       | none => none | some .exit => some .exit
       | some (.val r) => nockF k r (NT p)) := rfl

private theorem nF_Nwhile (k : Nat) (S : Noun) (t b : Term) :
    nockF (k+1) S (Nwhile t b) =
      (match nockF k S (cell (atom 1) (Lwhile t b)) with
       | none => none | some .exit => some .exit
       | some (.val r) => nockF k (cell r S) (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1))))) := rfl

private theorem nF_Nifte (k : Nat) (S : Noun) (q₁ q₂ : Term) :
    nockF (k+1) S (Nifte q₁ q₂) =
      (match nockF k S (cell (atom 0) (atom 2)) with
       | none => none | some .exit => some .exit
       | some (.val (atom 0)) => nockF k S (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT q₁)))
       | some (.val (atom 1)) => nockF k S (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT q₂)))
       | some (.val _) => some .exit) := rfl

private theorem nF_Lwhile (k : Nat) (A : Noun) (t b : Term) :
    nockF (k+1) A (Lwhile t b) =
      (match nockF k A (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT t))) with
       | none => none | some .exit => some .exit
       | some (.val T) => nockF k (cell T A)
         (cell (atom 6) (cell (cell (atom 0) (atom 4))
           (cell (cell (atom 9) (cell (atom 2)
                   (cell (cell (atom 0) (atom 6))
                         (cell (atom 7) (cell (cell (atom 0) (atom 5)) (NT b))))))
                 (cell (atom 0) (atom 5)))))) := rfl

-- ---------------------------------------------------------------------------
-- Inversion of the schema spines.  Each hands back recursive `nockF` facts at
-- strictly smaller fuel — that is what the fuel induction consumes.
-- ---------------------------------------------------------------------------

private theorem inv_Nifte {k : Nat} {q₁ q₂ : Term} {S : Noun} {y : Outcome}
    (h : nockF k S (Nifte q₁ q₂) = some y) :
    (∃ n, S = atom n ∧ y = .exit) ∨
    (∃ r m, m < k ∧ S = cell (atom 0) r ∧ nockF m r (NT q₁) = some y) ∨
    (∃ r m, m < k ∧ S = cell (atom 1) r ∧ nockF m r (NT q₂) = some y) ∨
    (∃ f r, S = cell f r ∧ f ≠ atom 0 ∧ f ≠ atom 1 ∧ y = .exit) := by
  cases k with
  | zero => simp [nockF] at h
  | succ k1 =>
  rw [nF_Nifte] at h
  cases k1 with
  | zero => simp [nockF] at h
  | succ k2 =>
  rw [nF_op0] at h
  cases S with
  | atom n =>
    rw [fasO_two_atom] at h
    simp only [Option.some.injEq] at h
    exact Or.inl ⟨n, rfl, h.symm⟩
  | cell f r =>
    rw [fasO_head] at h
    match f with
    | atom 0 =>
      dsimp only at h
      rw [nF_op7] at h
      cases k2 with
      | zero => simp [nockF] at h
      | succ k3 =>
        rw [nF_op0, fasO_tail] at h
        dsimp only at h
        exact Or.inr (Or.inl ⟨r, k3 + 1, by omega, rfl, h⟩)
    | atom 1 =>
      dsimp only at h
      rw [nF_op7] at h
      cases k2 with
      | zero => simp [nockF] at h
      | succ k3 =>
        rw [nF_op0, fasO_tail] at h
        dsimp only at h
        exact Or.inr (Or.inr (Or.inl ⟨r, k3 + 1, by omega, rfl, h⟩))
    | atom (n + 2) =>
      dsimp only at h
      simp only [Option.some.injEq] at h
      exact Or.inr (Or.inr (Or.inr ⟨atom (n + 2), r, rfl, by simp, by simp, h.symm⟩))
    | cell x z =>
      dsimp only at h
      simp only [Option.some.injEq] at h
      exact Or.inr (Or.inr (Or.inr ⟨cell x z, r, rfl, by simp, by simp, h.symm⟩))

/-- Inversion of the `L` spine.  Every recursive obligation — the test, the
    body, and the `L`-refire — appears at strictly smaller fuel, lifted to a
    common `m` by `nockF_mono`.  This is the anti-§1.3 device: the refire is
    *not* term-shaped, so it needs its own half of the induction. -/
private theorem inv_Lwhile {k : Nat} {t b : Term} {S : Noun} {o : Outcome}
    (h : nockF k (cell (Lwhile t b) S) (Lwhile t b) = some o) :
    ∃ m, m < k ∧
      ( (nockF m S (NT t) = some .exit ∧ o = .exit)
      ∨ (∃ n, nockF m S (NT t) = some (.val (atom n)) ∧ o = .exit)
      ∨ (∃ f S', nockF m S (NT t) = some (.val (cell f S')) ∧
            f ≠ atom 0 ∧ f ≠ atom 1 ∧ o = .exit)
      ∨ (∃ S', nockF m S (NT t) = some (.val (cell (atom 1) S')) ∧ o = .val S')
      ∨ (∃ S', nockF m S (NT t) = some (.val (cell (atom 0) S')) ∧
            nockF m S' (NT b) = some .exit ∧ o = .exit)
      ∨ (∃ S' S'', nockF m S (NT t) = some (.val (cell (atom 0) S')) ∧
            nockF m S' (NT b) = some (.val S'') ∧
            nockF m (cell (Lwhile t b) S'') (Lwhile t b) = some o) ) := by
  cases k with
  | zero => simp [nockF] at h
  | succ k1 =>
  rw [nF_Lwhile] at h
  cases k1 with
  | zero => simp [nockF] at h
  | succ k2 =>
  rw [nF_op7] at h
  cases k2 with
  | zero => simp [nockF] at h
  | succ k3 =>
  rw [nF_op0, fasO_tail] at h
  dsimp only at h
  -- h now dispatches on the test's outcome at fuel (k3+1)
  cases hT : nockF (k3 + 1) S (NT t) with
  | none => rw [hT] at h; simp at h
  | some x =>
    cases x with
    | exit =>
      rw [hT] at h; dsimp only at h
      simp only [Option.some.injEq] at h
      exact ⟨k3 + 1, by omega, Or.inl ⟨hT, h.symm⟩⟩
    | val T =>
      rw [hT] at h; dsimp only at h
      -- the loop body, on subject [T [L S]]
      rw [nF_op6, nF_op0] at h
      cases T with
      | atom n =>
        rw [fasO_four_atomhead] at h; dsimp only at h
        simp only [Option.some.injEq] at h
        exact ⟨k3 + 1, by omega, Or.inr (Or.inl ⟨n, hT, h.symm⟩)⟩
      | cell f S' =>
        rw [fasO_four] at h
        match f with
        | atom 1 =>
          -- exit branch: [0 5] recovers S'
          dsimp only at h
          rw [nF_op0, fasO_five] at h
          dsimp only at h
          simp only [Option.some.injEq] at h
          exact ⟨k3 + 1, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨S', hT, h.symm⟩)))⟩
        | atom (n + 2) =>
          dsimp only at h
          simp only [Option.some.injEq] at h
          exact ⟨k3 + 1, by omega,
            Or.inr (Or.inr (Or.inl ⟨atom (n + 2), S', hT, by simp, by simp, h.symm⟩))⟩
        | cell x z =>
          dsimp only at h
          simp only [Option.some.injEq] at h
          exact ⟨k3 + 1, by omega,
            Or.inr (Or.inr (Or.inl ⟨cell x z, S', hT, by simp, by simp, h.symm⟩))⟩
        | atom 0 =>
          -- continue branch: op9 over the autocons core rebuild
          dsimp only at h
          rw [nF_op9] at h
          cases k3 with
          | zero => simp [nockF] at h
          | succ k4 =>
          rw [nF_autocons] at h
          cases k4 with
          | zero => simp [nockF] at h
          | succ k5 =>
          rw [nF_op0, fasO_six] at h
          dsimp only at h
          rw [nF_op7] at h
          cases k5 with
          | zero => simp [nockF] at h
          | succ k6 =>
          rw [nF_op0, fasO_five] at h
          dsimp only at h
          cases hB : nockF (k6 + 1) S' (NT b) with
          | none => rw [hB] at h; simp at h
          | some z =>
            cases z with
            | exit =>
              rw [hB] at h; dsimp only at h
              simp only [Option.some.injEq] at h
              exact ⟨k6 + 1 + 1 + 1 + 1, by omega,
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨S', hT, nockF_mono hB (by omega), h.symm⟩))))⟩
            | val S'' =>
              rw [hB] at h; dsimp only at h
              rw [fasO_head] at h
              dsimp only at h
              exact ⟨k6 + 1 + 1 + 1 + 1, by omega,
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨S', S'', hT, nockF_mono hB (by omega), nockF_mono h (by omega)⟩))))⟩

private theorem nF_op1 (k : Nat) (S fol : Noun) :
    nockF (k+1) S (cell (atom 1) fol) = some (.val fol) := rfl

/-- `Λ_N(while …)` pins `L` and fires it against `[L S]` (claim W1). -/
private theorem inv_Nwhile {k : Nat} {t b : Term} {S : Noun} {y : Outcome}
    (h : nockF k S (Nwhile t b) = some y) :
    ∃ m, m < k ∧ nockF m (cell (Lwhile t b) S) (Lwhile t b) = some y := by
  cases k with
  | zero => simp [nockF] at h
  | succ k1 =>
  rw [nF_Nwhile] at h
  cases k1 with
  | zero => simp [nockF] at h
  | succ k2 =>
  rw [nF_op1] at h
  dsimp only at h
  rw [nF_op9] at h
  cases k2 with
  | zero => simp [nockF] at h
  | succ k3 =>
  rw [nF_op0, fasO_one] at h
  dsimp only at h
  rw [fasO_head] at h
  dsimp only at h
  exact ⟨k3 + 1, by omega, h⟩

-- ---------------------------------------------------------------------------
-- The backward simulation
-- ---------------------------------------------------------------------------

/-- The loop outcome, packaged parametrically over continuations.  `o` is the
    *`L`-firing's* outcome; the two clauses discharge it into `while_*`
    constructors for any `p`. -/
def LoopBack (t b : Term) (S : Noun) (o : Outcome) : Prop :=
  ∀ p : Term,
    (o = .exit → CEval (.while t b p) S .exit) ∧
    (∀ E, o = .val E → ∀ {o'}, CEval p E o' → CEval (.while t b p) S o')

/-- The two-part fuel induction.  Every recursive obligation — a term-level
    call inside a schema, or the `L`-refire — appears in `nockF`'s computation
    at strictly smaller fuel, so strong induction on `k` supplies every IH at
    every nesting depth, uniformly.  The `L`-refire is not term-shaped, which
    is why the second half exists. -/
theorem backward_fuel : ∀ k : Nat,
    (∀ {t : Term} {S o}, nockF k S (NT t) = some o → CEval t S o) ∧
    (∀ {t b : Term} {S o},
       nockF k (cell (Lwhile t b) S) (Lwhile t b) = some o →
       LoopBack t b S o) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  constructor
  -- ── term half ────────────────────────────────────────────────────────────
  · intro t S o h
    match t with
    | .nil =>
      cases k with
      | zero => simp [nockF] at h
      | succ j =>
        simp only [NT_nil] at h
        rw [nF_op0, fasO_one] at h
        dsimp only at h
        simp only [Option.some.injEq] at h
        exact h ▸ CEval.nil
    | .seq w p =>
      cases k with
      | zero => simp [nockF] at h
      | succ j =>
        rw [nF_NT_seq] at h
        cases hw : nockF j S (phi w) with
        | none => rw [hw] at h; simp at h
        | some x =>
          have hx : x = cw w S :=
            NockEval.deterministic (nockF_sound j hw) (leaf_correct w S)
          cases x with
          | exit =>
            rw [hw] at h; dsimp only at h
            simp only [Option.some.injEq] at h
            exact h ▸ CEval.seq_crash hx.symm
          | val r =>
            rw [hw] at h; dsimp only at h
            exact CEval.seq hx.symm ((ih j (by omega)).1 h)
    | .ifte q₁ q₂ p =>
      cases k with
      | zero => simp [nockF] at h
      | succ j =>
        rw [nF_NT_ifte] at h
        cases hI : nockF j S (Nifte q₁ q₂) with
        | none => rw [hI] at h; simp at h
        | some y =>
          rcases inv_Nifte hI with
            ⟨n, rfl, rfl⟩ | ⟨r, m, hm, rfl, hq⟩ | ⟨r, m, hm, rfl, hq⟩ | ⟨f, r, rfl, hne0, hne1, rfl⟩
          · rw [hI] at h; dsimp only at h
            simp only [Option.some.injEq] at h
            exact h ▸ CEval.ifte_atom
          · cases y with
            | exit =>
              rw [hI] at h; dsimp only at h
              simp only [Option.some.injEq] at h
              exact h ▸ CEval.ifte_then_crash ((ih m (by omega)).1 hq)
            | val T =>
              rw [hI] at h; dsimp only at h
              exact CEval.ifte_then ((ih m (by omega)).1 hq) ((ih j (by omega)).1 h)
          · cases y with
            | exit =>
              rw [hI] at h; dsimp only at h
              simp only [Option.some.injEq] at h
              exact h ▸ CEval.ifte_else_crash ((ih m (by omega)).1 hq)
            | val T =>
              rw [hI] at h; dsimp only at h
              exact CEval.ifte_else ((ih m (by omega)).1 hq) ((ih j (by omega)).1 h)
          · rw [hI] at h; dsimp only at h
            simp only [Option.some.injEq] at h
            exact h ▸ CEval.ifte_nonloob hne0 hne1
    | .while t b p =>
      cases k with
      | zero => simp [nockF] at h
      | succ j =>
        rw [nF_NT_while] at h
        cases hW : nockF j S (Nwhile t b) with
        | none => rw [hW] at h; simp at h
        | some y =>
          obtain ⟨m, hm, hL⟩ := inv_Nwhile hW
          have hlb : LoopBack t b S y := (ih m (by omega)).2 hL
          cases y with
          | exit =>
            rw [hW] at h; dsimp only at h
            simp only [Option.some.injEq] at h
            exact h ▸ (hlb p).1 rfl
          | val E =>
            rw [hW] at h; dsimp only at h
            exact (hlb p).2 E rfl ((ih j (by omega)).1 h)
  -- ── loop half ────────────────────────────────────────────────────────────
  · intro t b S o h
    obtain ⟨m, hm, hcase⟩ := inv_Lwhile h
    intro p
    rcases hcase with
      ⟨ht, rfl⟩
    | ⟨n, ht, rfl⟩
    | ⟨f, S', ht, hne0, hne1, rfl⟩
    | ⟨S', ht, rfl⟩
    | ⟨S', ht, hb, rfl⟩
    | ⟨S', S'', ht, hb, hre⟩
    · exact ⟨fun _ => CEval.while_test_crash ((ih m hm).1 ht),
             fun E hE => (by cases hE)⟩
    · exact ⟨fun _ => CEval.while_flag_atom ((ih m hm).1 ht),
             fun E hE => (by cases hE)⟩
    · exact ⟨fun _ => CEval.while_nonloob ((ih m hm).1 ht) hne0 hne1,
             fun E hE => (by cases hE)⟩
    · refine ⟨fun hE => (by cases hE), fun E hE => ?_⟩
      simp only [Outcome.val.injEq] at hE
      subst hE
      exact fun h' => CEval.while_exit ((ih m hm).1 ht) h'
    · exact ⟨fun _ => CEval.while_body_crash ((ih m hm).1 ht) ((ih m hm).1 hb),
             fun E hE => (by cases hE)⟩
    · have hlb : LoopBack t b S'' o := (ih m hm).2 hre
      refine ⟨fun hEx => ?_, fun E hE => ?_⟩
      · exact CEval.while_step ((ih m hm).1 ht) ((ih m hm).1 hb) (hEx ▸ (hlb p).1 hEx)
      · exact fun h' => CEval.while_step ((ih m hm).1 ht) ((ih m hm).1 hb)
          ((hlb p).2 E hE h')

/-- **Backward simulation.**  Do not induct on the derivation: convert it to
    fuel, and induct there. -/
theorem nockeval_complete {t : Term} {S o}
    (h : NockEval S (NT t) o) : CEval t S o :=
  let ⟨k, hk⟩ := nockF_complete h
  (backward_fuel k).1 hk
