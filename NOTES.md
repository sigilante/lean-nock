◐ The user wants to implement `NockEval` as an inductive relation. Let me think carefully about this.

  The key insight is that `NockEval` should mirror all the Nock 4K rules as constructors. Let me think about what the 
  constructors need to be:

  1. Auto-cons: `*[a [b c] d] = [*[a b c] *[a d]]`
     - Need: `NockEval a (cell b c) r1` and `NockEval a fol r2`
     - Produces: `NockEval a (cell (cell b c) fol) (cell r1 r2)`
     
  2. Opcode 0: `*[a 0 b] = /[b a]` - this performs address lookup on the subject
  3. Opcode 1: `*[a 1 b] = b` - this just returns the formula unchanged
  4. Opcode 2: `*[a 2 b c] = *[*[a b] c]` - this evaluates b against a, then evaluates c against that result
  5. Opcode 3: `*[a 3 b] = ?*[a b]` - this checks if the result of evaluating b against a is a cell or atom
  6. Opcode 4: `*[a 4 b] = +*[a b]` - this increments the result of evaluating b against a, but only works when the 
  result is an atom

  ; for a relational semantics we can just state the rule and let it panic on cells
  7. Opcode 5: `*[a 5 b c] = =[*[a b] *[a c]]` - this checks equality between the results of evaluating b and c against a

  , producing a cell of those two results and then applying the equality test
  8. Opcode 6: `*[a 6 b c d] = *[a *[[c d] 0 *[[2 3] 0 *[a 4 4 b]]]]` - this is if-then-else logic where we evaluate b, 
  and if it's 0 we take the c branch, otherwise we take the d branch. I can represent this with two rules: one for when b
   evaluates to 0 that produces the result of c, and another for when b evaluates to 1 that produces the result of d

  .

  9. Opcode 7: `*[a 7 b c] = *[*[a b] c]` - this is composition, where I evaluate b against a to get an intermediate 
  result, then evaluate c against that result.

  10. Opcode 8: `*[a 8 b c] = *[[*[a b] a] c]` - I need to evaluate b against a, then construct a cell pairing that 
  result with a, and finally evaluate c against that new cell.

  11. Opcode 9: `*[a 9 b c] = *[*[a c] 2 [0 1] 0 b]` - this evaluates c to produce a core, then invokes arm b of that 
  core. The key insight is that this becomes a computation that evaluates the core against itself using the arm selector.
   So op9 completes with the result being the evaluation of the core with the computed address. Now I'm working through 
  opcode 10, which applies a function to two evaluated arguments and wraps the results. Then opcode 11 has two branches 
  depending on whether the hint is static or dynamic, with the dynamic case recursing on a constructed cell.


  What we can prove now (that we couldn't before):

   1. Properties by induction on derivation trees. NockEval.rec is fully generated — you can prove things
   by structural induction over execution traces. Determinism (NockEval a f r1 → NockEval a f r2 → r1 = 
  r2), monotonicity, trace composition — all of these become inductions over the constructors. With an 
  opaque function + axioms, induction was impossible.
   2. callGate_gate_eval with no custom axioms. Before: callGate_gate depended on 6 custom axiom 
  declarations. Now: depends only on propext, Quot.sound — Lean4's own foundations. That's not just 
  cleaner, it's meaningfully different: the proof is actually checked by the kernel.
   3. ZK circuit correspondence. Each NockEval constructor directly maps to a circuit constraint. A ZK 
  proof that a Nock computation happened is literally a proof that a NockEval derivation exists. The 
  axiom version proved things about an opaque function — the circuit has no obvious target. The inductive
   version is the circuit spec.

  What we still cannot prove:

   - Soundness of the interpreter: nock a f = r → NockEval a f r. This would require nock to be 
  transparent. The interpreter and the relation are currently independent — we believe they agree 
  (confirmed by #eval), but haven't proved it. This is the remaining gap.

  Why this gap is acceptable for the zkVM goal:

  The ZK circuit will be verified against NockEval directly — not against the Lean evaluator. The
  evaluator is just for testing. So the proof target (NockEval derivations exist for valid Nock
  computations) is exactly what we have.


  ● There are three tiers of things to prove, in increasing ambition:

  ------------------------------------------------------------------------------------------------------

  Tier 1 — Arithmetic correctness (tractable, high value)

  These are the classical PL verification targets — prove the Nock-compiled gate computes the right
  mathematical function:

  ┌─────────────┬────────────────────────────────────────────────┐
  │ Gate        │ Property                                       │
  ├─────────────┼────────────────────────────────────────────────┤
  │ dec         │ dec (n+1) = n                                  │
  ├─────────────┼────────────────────────────────────────────────┤
  │ add         │ add m n = m + n                                │
  ├─────────────┼────────────────────────────────────────────────┤
  │ mul         │ mul m n = m * n                                │
  ├─────────────┼────────────────────────────────────────────────┤
  │ div/mod     │ n = (div n d) * d + (mod n d), mod n d < d     │
  ├─────────────┼────────────────────────────────────────────────┤
  │ lth         │ lth m n = 0 ↔ m < n                            │
  └─────────────┴────────────────────────────────────────────────┘

  This is what CompCert does for C. The chain: Hoon source → compiled Nock formula → NockEval derivation
  → = n on a Nat. dec is already our immediate target.

  ------------------------------------------------------------------------------------------------------

  Tier 2 — Algebraic laws (medium difficulty)

  Prove the compiled gates satisfy the algebraic identities Hoon claims they do:

   - add m n = add n m (commutativity)
   - add (add m n) k = add m (add n k) (associativity)  
   - mul m (add n k) = add (mul m n) (mul m k) (distributivity)
   - sub (add n k) n = k (cancellation)

  These require the Tier 1 results as lemmas — they're statements about NockEval, not directly about Nat.

  ------------------------------------------------------------------------------------------------------

  Tier 3 — zkVM-specific (the real goal)

  What the Leo project is after: prove that the circuit correctly encodes execution. Concretely:

   - Soundness: if the circuit accepts a trace, then NockEval holds for it
   - Completeness: every valid NockEval derivation can be encoded as a satisfying circuit assignment
   - Specific computation witnesses: "there exists a valid NockEval trace proving dec 42 = 41" — where 
  the trace itself is the ZK witness

  ------------------------------------------------------------------------------------------------------

  What's off the table for now

   - Cryptographic jets (SHA-256 etc.) — the Nock formulas are enormous; the proofs would be too
   - Hoon's type system — ++nest, ++mull, ++play are hundreds of arms; proof of type soundness is a 
  multi-year project
   - Anything with ~ (divergence) — requires the fuel-based semantics to even state

  ------------------------------------------------------------------------------------------------------

  The natural progression from here:

   dec correct  →  add correct  →  algebraic laws  →  circuit soundness/completeness

  dec is the right first target because it exercises the loop pattern (op 8 push, op 9 recurse) that
  everything else uses. Once you have dec, add follows the same proof structure. After add and mul, you
  have enough to state the algebraic laws.

  Want to push toward dec correctness now, or is the fuel-based refactor a prerequisite you want to
  tackle first?
