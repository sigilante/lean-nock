import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Comp

namespace Nock
open Noun

/-!
# The term algebra and its compiler

`Term` and the compilation schemas, migrated verbatim from `Nock/Oracle.lean`
per SPEC-PHASE4B-PROOFS §1.  They were acquitted by the Class D oracle trial
(676 runs, five fuel schedules, zero mismatches — `TABLE-REPORT.md` §D), so
they move into the proof chain unedited.

## Naming

`NT : Term → Noun` is the paper's `Λ_N` over the term algebra.  The Phase 4a
`N : Prog → Noun` in `Nock/Comp.lean` is **frozen** — its statements are API —
and `Term.ofProg` / `NT_ofProg` connect the two, so the term algebra is a
conservative extension of the free monoid of words.
-/

/-- Continuation-carrying terms, mirroring the paper's grammar
    `p ::= ε | w·p | ifte(q₁,q₂)·p | while(p_t,p_b)·p`. -/
inductive Term
  | nil   : Term
  | seq   : Word → Term → Term
  | ifte  : Term → Term → Term → Term
  | while : Term → Term → Term → Term
  deriving Repr

/-- The term compiler, `Λ_N`.  Schemas verbatim from DEFENDANT-CLASSD §2. -/
def NT : Term → Noun
  | .nil       => cell (atom 0) (atom 1)
  | .seq w p   => cell (atom 7) (cell (phi w) (NT p))
  -- Λ_N(ifte(q₁,q₂)) = [6 [0 2] [7 [0 3] Λ_N(q₁)] [7 [0 3] Λ_N(q₂)]]
  | .ifte q₁ q₂ p =>
      cell (atom 7) (cell
        (cell (atom 6) (cell
          (cell (atom 0) (atom 2))
          (cell (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT q₁)))
                (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT q₂))))))
        (NT p))
  -- Λ_N(while(p_t,p_b)) = [8 [1 L] 9 2 0 1]
  | .while t b p =>
      cell (atom 7) (cell
        (cell (atom 8) (cell
          (cell (atom 1)
            (cell (atom 8) (cell
              (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT t)))
              (cell (atom 6) (cell
                (cell (atom 0) (atom 4))
                (cell (cell (atom 9) (cell (atom 2)
                        (cell (cell (atom 0) (atom 6))
                              (cell (atom 7) (cell (cell (atom 0) (atom 5)) (NT b))))))
                      (cell (atom 0) (atom 5))))))))
          (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1))))))
        (NT p))

/-- `Λ_N(ifte(q₁,q₂))` — the branch schema, without its continuation. -/
def Nifte (q₁ q₂ : Term) : Noun :=
  cell (atom 6) (cell
    (cell (atom 0) (atom 2))
    (cell (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT q₁)))
          (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT q₂)))))

/-- `L` — the loop body pinned by `Λ_N(while …)`'s outer `op8`.  Fired against
    the subject `[L S]`, so inside `L` the stack sits at axis 3. -/
def Lwhile (t b : Term) : Noun :=
  cell (atom 8) (cell
    (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT t)))
    (cell (atom 6) (cell
      (cell (atom 0) (atom 4))
      (cell (cell (atom 9) (cell (atom 2)
              (cell (cell (atom 0) (atom 6))
                    (cell (atom 7) (cell (cell (atom 0) (atom 5)) (NT b))))))
            (cell (atom 0) (atom 5))))))

/-- `Λ_N(while(p_t,p_b))` — pin `L`, then fire it against `[L S]`. -/
def Nwhile (t b : Term) : Noun :=
  cell (atom 8) (cell
    (cell (atom 1) (Lwhile t b))
    (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))))

-- Unfolding equations.  `NT` was written inline so that `Nifte`/`Nwhile` could
-- be defined in terms of it without mutual recursion; these tie the knot.
theorem NT_nil : NT .nil = cell (atom 0) (atom 1) := rfl
theorem NT_seq (w : Word) (p : Term) :
    NT (.seq w p) = cell (atom 7) (cell (phi w) (NT p)) := rfl
theorem NT_ifte (q₁ q₂ p : Term) :
    NT (.ifte q₁ q₂ p) = cell (atom 7) (cell (Nifte q₁ q₂) (NT p)) := rfl
theorem NT_while (t b p : Term) :
    NT (.while t b p) = cell (atom 7) (cell (Nwhile t b) (NT p)) := rfl

-- ---------------------------------------------------------------------------
-- Embedding: the term algebra conservatively extends the free monoid of words
-- ---------------------------------------------------------------------------

def Term.ofProg (p : Prog) : Term := p.foldr .seq .nil

theorem NT_ofProg (p : Prog) : NT (Term.ofProg p) = N p := by
  induction p with
  | nil => rfl
  | cons w p ih =>
    show NT (.seq w (Term.ofProg p)) = N (w :: p)
    rw [NT_seq, ih]; rfl

end Nock
