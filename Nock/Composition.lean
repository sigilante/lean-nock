import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.Comp
import Nock.Term
import Nock.CEval
import Nock.Backward
open Noun

/-!
# The Class D composition theorem

The paper's Class D claim, as a kernel-checked biconditional over the full term
algebra, plus its divergence corollary.  This upgrades the compilation schemas
of Equations (classd-ifte) and (classd-while) from **confirmed (oracle)** to
**discharged (kernel)**.
-/

/-- `CEval` is deterministic.  **Transferred**, not proved directly: a direct
    proof is a 15×15 constructor bash, and the whole architecture exists to
    avoid it.  Determinism of `NockEval` is the Phase 2 result. -/
theorem ceval_det {t S o₁ o₂} (h₁ : CEval t S o₁) (h₂ : CEval t S o₂) : o₁ = o₂ :=
  NockEval.deterministic (ceval_sound h₁) (ceval_sound h₂)

/-- **The composition theorem.**  A Nock derivation of the compiled term and a
    C derivation of the term agree, in both directions, on values and crashes. -/
theorem composition_term (t : Term) (S : Noun) (o : Outcome) :
    NockEval S (NT t) o ↔ CEval t S o :=
  ⟨nockeval_complete, ceval_sound⟩

/-- Divergence on the C side: no outcome is derivable. -/
def CDiverges (t : Term) (S : Noun) : Prop := ∀ o, ¬ CEval t S o

/-- **Equal least fixed points, made literal.**  The two semantics agree on
    values, on crashes, *and on divergence* — the last as a biconditional
    between two absence-of-derivation statements.

    This is the sentence the manuscript's Class D proof-burden paragraph gets
    to cite, which is why it has its own name despite being a one-liner. -/
theorem composition_diverges (t : Term) (S : Noun) :
    Diverges S (NT t) ↔ CDiverges t S := by
  constructor
  · intro hd o hc; exact hd o (ceval_sound hc)
  · intro hc o hn; exact hc o (nockeval_complete hn)

-- ---------------------------------------------------------------------------
-- Embedding compatibility: the term algebra conservatively extends the monoid
-- ---------------------------------------------------------------------------

theorem ceval_ofProg (p : Prog) (S : Noun) : CEval (Term.ofProg p) S (Csem p S) := by
  induction p generalizing S with
  | nil => exact CEval.nil
  | cons w p ih =>
    show CEval (.seq w (Term.ofProg p)) S (Csem (w :: p) S)
    simp only [Csem]
    cases hcw : cw w S with
    | val S' => exact CEval.seq hcw (ih S')
    | exit   => exact CEval.seq_crash hcw

/-- The regression check: the Phase 4a `composition_agree` is recovered from the
    term-algebra machinery, so `Term` conservatively extends `Prog`. -/
theorem composition_ofProg (p : Prog) (S : Noun) {o : Outcome}
    (h : NockEval S (N p) o) : o = Csem p S := by
  rw [← NT_ofProg] at h
  exact ceval_det (nockeval_complete h) (ceval_ofProg p S)
