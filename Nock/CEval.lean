import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.Comp
import Nock.Term
open Noun

/-!
# `CEval` and the forward simulation

`CEval t S o` is the big-step semantics of the C side over the term algebra,
transcribed from the manuscript's C listings (DEFENDANT-CLASSD §4).  It is
divergence-by-absence and left-to-right strict, mirroring `NockEval`.

This file proves the **forward** direction, `CEval → NockEval`.

## Why the motive is strengthened

The naive induction fails in the `while_step` case: the recursion re-fires `L`
against `[L S'']`, and that derivation is not recoverable from the induction
hypothesis's *conclusion* without deep inversion.  So the motive carries a
second conjunct — the loop-level fact: the `L`-firing's own outcome `oL`, plus
its link to the composite outcome through the continuation.

With the conjunct in place, `while_step`'s recursion is an **immediate**
sub-derivation use: `ih₃.2` hands over the inner `L`-derivation, and the outer
one is assembled by constructor application alone.

This is the same class of fix as the SPEC-PHASE4 §1.3 correction — a
*strengthened* motive, which cannot make a false theorem provable.  This time
it is in the spec rather than discovered against it.
-/

/-- Big-step semantics of the C side.  Fifteen constructors, transcribed
    verbatim.  The flag lives in the *subject index* for `ifte` (mirroring the C
    `pop`) and in the *test's derived value* for `while` (mirroring `p_t`'s
    output).  An infinite loop has no finite `while_step` chain, hence no
    derivation — divergence by absence, on both sides. -/
inductive CEval : Term → Noun → Outcome → Prop where
  | nil {S} : CEval .nil S (.val S)

  | seq {w p S S' o} :
      cw w S = .val S' → CEval p S' o → CEval (.seq w p) S o
  | seq_crash {w p S} :
      cw w S = .exit → CEval (.seq w p) S .exit

  | ifte_then {q₁ q₂ p r T o} :
      CEval q₁ r (.val T) → CEval p T o →
      CEval (.ifte q₁ q₂ p) (cell (atom 0) r) o
  | ifte_then_crash {q₁ q₂ p r} :
      CEval q₁ r .exit → CEval (.ifte q₁ q₂ p) (cell (atom 0) r) .exit
  | ifte_else {q₁ q₂ p r T o} :
      CEval q₂ r (.val T) → CEval p T o →
      CEval (.ifte q₁ q₂ p) (cell (atom 1) r) o
  | ifte_else_crash {q₁ q₂ p r} :
      CEval q₂ r .exit → CEval (.ifte q₁ q₂ p) (cell (atom 1) r) .exit
  | ifte_nonloob {q₁ q₂ p f r} :
      f ≠ atom 0 → f ≠ atom 1 →
      CEval (.ifte q₁ q₂ p) (cell f r) .exit
  | ifte_atom {q₁ q₂ p n} :
      CEval (.ifte q₁ q₂ p) (atom n) .exit

  | while_step {t b p S S' S'' o} :
      CEval t S (.val (cell (atom 0) S')) →
      CEval b S' (.val S'') →
      CEval (.while t b p) S'' o →
      CEval (.while t b p) S o
  | while_exit {t b p S S' o} :
      CEval t S (.val (cell (atom 1) S')) →
      CEval p S' o →
      CEval (.while t b p) S o
  | while_test_crash {t b p S} :
      CEval t S .exit → CEval (.while t b p) S .exit
  | while_body_crash {t b p S S'} :
      CEval t S (.val (cell (atom 0) S')) → CEval b S' .exit →
      CEval (.while t b p) S .exit
  | while_flag_atom {t b p S n} :
      CEval t S (.val (atom n)) → CEval (.while t b p) S .exit
  | while_nonloob {t b p S f S'} :
      CEval t S (.val (cell f S')) → f ≠ atom 0 → f ≠ atom 1 →
      CEval (.while t b p) S .exit

-- ---------------------------------------------------------------------------
-- Loop plumbing
-- ---------------------------------------------------------------------------

/-- Firing `L` against `[L S]` is what `Λ_N(while …)` does: pin `L` with `op8`,
    then `op9` arm 2. -/
private theorem L_fire {t b : Term} {S : Noun} {oL : Outcome}
    (h : NockEval (cell (Lwhile t b) S) (Lwhile t b) oL) :
    NockEval S (Nwhile t b) oL :=
  NockEval.op8 NockEval.op1
    (NockEval.op9 (NockEval.op0 (fasO_one _)) (fasO_head _ _) h)

/-- Inside `L` the stack sits at axis 3 (claim W2), so `[7 [0 3] Λ_N(p_t)]`
    evaluates the test against `S`. -/
private theorem L_test {t b : Term} {S : Noun} {ot : Outcome}
    (h : NockEval S (NT t) ot) :
    NockEval (cell (Lwhile t b) S)
      (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT t))) ot :=
  NockEval.op7 (NockEval.op0 (fasO_tail _ _)) h

/-- The `L`-firing's outcome, discharged into `Λ_N(while …)` through the
    continuation. -/
private theorem while_from_L {t b p : Term} {S : Noun} {o oL : Outcome}
    (hL : NockEval (cell (Lwhile t b) S) (Lwhile t b) oL)
    (link : (oL = .exit ∧ o = .exit) ∨ (∃ E, oL = .val E ∧ NockEval E (NT p) o)) :
    NockEval S (NT (.while t b p)) o := by
  rw [NT_while]
  rcases link with ⟨rfl, rfl⟩ | ⟨E, rfl, hE⟩
  · exact NockEval.op7_crash (L_fire hL)
  · exact NockEval.op7 (L_fire hL) hE

-- ---------------------------------------------------------------------------
-- Forward: CEval → NockEval
-- ---------------------------------------------------------------------------

/-- The strengthened motive.  Conjunct 2 is the loop-level fact; it is what
    makes `while_step`'s recursion an immediate-IH use.  Do not weaken it. -/
theorem ceval_sound_aux {t S o} (h : CEval t S o) :
    NockEval S (NT t) o ∧
    (∀ t' b' p, t = .while t' b' p →
      ∃ oL, NockEval (cell (Lwhile t' b') S) (Lwhile t' b') oL ∧
        ((oL = .exit ∧ o = .exit) ∨
         (∃ E, oL = .val E ∧ NockEval E (NT p) o))) := by
  induction h with
  | nil =>
    exact ⟨NockEval.op0 (fasO_one _), fun _ _ _ heq => Term.noConfusion heq⟩
  | @seq w p S S' o hcw _ ih =>
    refine ⟨?_, fun _ _ _ heq => Term.noConfusion heq⟩
    rw [NT_seq]
    have hw : NockEval S (phi w) (.val S') := hcw ▸ leaf_correct w S
    exact NockEval.op7 hw ih.1
  | @seq_crash w p S hcw =>
    refine ⟨?_, fun _ _ _ heq => Term.noConfusion heq⟩
    rw [NT_seq]
    have hw : NockEval S (phi w) .exit := hcw ▸ leaf_correct w S
    exact NockEval.op7_crash hw
  -- ifte: `cases` has already fixed the subject shape
  | @ifte_then q₁ q₂ p r T o _ _ ih1 ih2 =>
    refine ⟨?_, fun _ _ _ heq => Term.noConfusion heq⟩
    rw [NT_ifte]
    exact NockEval.op7
      (NockEval.op6_then (NockEval.op0 (fasO_head (atom 0) r))
        (NockEval.op7 (NockEval.op0 (fasO_tail (atom 0) r)) ih1.1)) ih2.1
  | @ifte_then_crash q₁ q₂ p r _ ih1 =>
    refine ⟨?_, fun _ _ _ heq => Term.noConfusion heq⟩
    rw [NT_ifte]
    exact NockEval.op7_crash
      (NockEval.op6_then (NockEval.op0 (fasO_head (atom 0) r))
        (NockEval.op7 (NockEval.op0 (fasO_tail (atom 0) r)) ih1.1))
  | @ifte_else q₁ q₂ p r T o _ _ ih1 ih2 =>
    refine ⟨?_, fun _ _ _ heq => Term.noConfusion heq⟩
    rw [NT_ifte]
    exact NockEval.op7
      (NockEval.op6_else (NockEval.op0 (fasO_head (atom 1) r))
        (NockEval.op7 (NockEval.op0 (fasO_tail (atom 1) r)) ih1.1)) ih2.1
  | @ifte_else_crash q₁ q₂ p r _ ih1 =>
    refine ⟨?_, fun _ _ _ heq => Term.noConfusion heq⟩
    rw [NT_ifte]
    exact NockEval.op7_crash
      (NockEval.op6_else (NockEval.op0 (fasO_head (atom 1) r))
        (NockEval.op7 (NockEval.op0 (fasO_tail (atom 1) r)) ih1.1))
  | @ifte_nonloob q₁ q₂ p f r hne0 hne1 =>
    refine ⟨?_, fun _ _ _ heq => Term.noConfusion heq⟩
    rw [NT_ifte]
    exact NockEval.op7_crash
      (NockEval.op6_nonloob (NockEval.op0 (fasO_head f r)) hne0 hne1)
  | @ifte_atom q₁ q₂ p n =>
    refine ⟨?_, fun _ _ _ heq => Term.noConfusion heq⟩
    rw [NT_ifte]
    exact NockEval.op7_crash
      (NockEval.op6_crash (NockEval.op0_crash (fasO_two_atom n)))
  -- while: conjunct 2 carries the loop-level fact
  | @while_step t b p S S' S'' o _ _ _ ih1 ih2 ih3 =>
    obtain ⟨oL, hL'', link⟩ := ih3.2 t b p rfl
    -- assemble the L-firing at S from the one at S''
    have hL : NockEval (cell (Lwhile t b) S) (Lwhile t b) oL :=
      NockEval.op8 (L_test ih1.1)
        (NockEval.op6_then
          (NockEval.op0 (fasO_four (atom 0) S' (cell (Lwhile t b) S)))
          (NockEval.op9
            (NockEval.autocons
              (NockEval.op0 (fasO_six (cell (atom 0) S') (Lwhile t b) S))
              (NockEval.op7
                (NockEval.op0 (fasO_five (atom 0) S' (cell (Lwhile t b) S))) ih2.1))
            (fasO_head (Lwhile t b) S'') hL''))
    refine ⟨while_from_L hL link, ?_⟩
    intro t' b' p' heq
    injection heq with h1 h2 h3; subst h1; subst h2; subst h3
    exact ⟨oL, hL, link⟩
  | @while_exit t b p S S' o _ _ ih1 ih2 =>
    have hL : NockEval (cell (Lwhile t b) S) (Lwhile t b) (.val S') :=
      NockEval.op8 (L_test ih1.1)
        (NockEval.op6_else
          (NockEval.op0 (fasO_four (atom 1) S' (cell (Lwhile t b) S)))
          (NockEval.op0 (fasO_five (atom 1) S' (cell (Lwhile t b) S))))
    have link : ((Outcome.val S') = .exit ∧ o = .exit) ∨
        (∃ E, (Outcome.val S') = .val E ∧ NockEval E (NT p) o) :=
      Or.inr ⟨S', rfl, ih2.1⟩
    refine ⟨while_from_L hL link, ?_⟩
    intro t' b' p' heq
    injection heq with h1 h2 h3; subst h1; subst h2; subst h3
    exact ⟨_, hL, link⟩
  | @while_test_crash t b p S _ ih1 =>
    have hL : NockEval (cell (Lwhile t b) S) (Lwhile t b) .exit :=
      NockEval.op8_crash (L_test ih1.1)
    have link : ((Outcome.exit) = .exit ∧ (Outcome.exit) = .exit) ∨
        (∃ E, (Outcome.exit) = .val E ∧ NockEval E (NT p) .exit) := Or.inl ⟨rfl, rfl⟩
    refine ⟨while_from_L hL link, ?_⟩
    intro t' b' p' heq
    injection heq with h1 h2 h3; subst h1; subst h2; subst h3
    exact ⟨_, hL, link⟩
  | @while_body_crash t b p S S' _ _ ih1 ih2 =>
    have hL : NockEval (cell (Lwhile t b) S) (Lwhile t b) .exit :=
      NockEval.op8 (L_test ih1.1)
        (NockEval.op6_then
          (NockEval.op0 (fasO_four (atom 0) S' (cell (Lwhile t b) S)))
          (NockEval.op9_crash
            (NockEval.autocons_crashR
              (NockEval.op0 (fasO_six (cell (atom 0) S') (Lwhile t b) S))
              (NockEval.op7
                (NockEval.op0 (fasO_five (atom 0) S' (cell (Lwhile t b) S))) ih2.1))))
    have link : ((Outcome.exit) = .exit ∧ (Outcome.exit) = .exit) ∨
        (∃ E, (Outcome.exit) = .val E ∧ NockEval E (NT p) .exit) := Or.inl ⟨rfl, rfl⟩
    refine ⟨while_from_L hL link, ?_⟩
    intro t' b' p' heq
    injection heq with h1 h2 h3; subst h1; subst h2; subst h3
    exact ⟨_, hL, link⟩
  | @while_flag_atom t b p S n _ ih1 =>
    have hL : NockEval (cell (Lwhile t b) S) (Lwhile t b) .exit :=
      NockEval.op8 (L_test ih1.1)
        (NockEval.op6_crash
          (NockEval.op0_crash (fasO_four_atomhead n (cell (Lwhile t b) S))))
    have link : ((Outcome.exit) = .exit ∧ (Outcome.exit) = .exit) ∨
        (∃ E, (Outcome.exit) = .val E ∧ NockEval E (NT p) .exit) := Or.inl ⟨rfl, rfl⟩
    refine ⟨while_from_L hL link, ?_⟩
    intro t' b' p' heq
    injection heq with h1 h2 h3; subst h1; subst h2; subst h3
    exact ⟨_, hL, link⟩
  | @while_nonloob t b p S f S' _ hne0 hne1 ih1 =>
    have hL : NockEval (cell (Lwhile t b) S) (Lwhile t b) .exit :=
      NockEval.op8 (L_test ih1.1)
        (NockEval.op6_nonloob
          (NockEval.op0 (fasO_four f S' (cell (Lwhile t b) S))) hne0 hne1)
    have link : ((Outcome.exit) = .exit ∧ (Outcome.exit) = .exit) ∨
        (∃ E, (Outcome.exit) = .val E ∧ NockEval E (NT p) .exit) := Or.inl ⟨rfl, rfl⟩
    refine ⟨while_from_L hL link, ?_⟩
    intro t' b' p' heq
    injection heq with h1 h2 h3; subst h1; subst h2; subst h3
    exact ⟨_, hL, link⟩

/-- **Forward simulation.**  Every C derivation is matched by a Nock derivation
    of the compiled term, with the same outcome. -/
theorem ceval_sound {t S o} (h : CEval t S o) : NockEval S (NT t) o :=
  (ceval_sound_aux h).1
