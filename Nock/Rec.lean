import Nock.Basic
import Nock.Proofs
import Nock.Eval
import Nock.Fuel
import Nock.Comp
import Nock.Term
import Nock.CEval
import Nock.Backward
import Nock.Composition
open Noun

/-!
# Named definitions: self- and mutually recursive words

The manuscript's *Named Definitions* subsection argues that Forth colon
definitions add no new machinery: a self-recursive definition is an opcode-9
refiring of the enclosing core, mutual recursion is a simultaneous fixpoint
over a multi-armed battery, and one fixpoint argument covers both.  This module
mechanizes that extension.

## Language

`RTerm` extends the term algebra with calls into a table of definitions
`D : List RTerm`.  Every definition may call every other, so the table is one
simultaneous fixpoint.  Call-free code is embedded as blocks `blk t`, compiled
by `Λ_N` — so `while` loops are available inside a block.  Sequencing and
`ifte` may contain calls.  A loop whose body calls a definition is written as a
recursive definition.  A call to an index with no definition crashes.

## Compilation

The table compiles to a battery `B = [NR d₀ [NR d₁ … 0]]`.  Code runs against
the core `[B S]` and returns `[B S']`.

- `blk t`: `[[0 2] [7 [0 3] Λ_N(t)]]` — run the block on the stack, keep `B`.
- `call i`: `[9 armAx(i) 0 1]` — refire the core at arm `i`'s axis.
- `ifte`: test the flag at axis 6; each branch pops it with `[[0 2] 0 7]`.

No arm contains the battery — calls reach it through the subject — so `B` is a
finite constant, pinned once by the program entry
`[7 [[1 B] 0 1] [7 NR(main) 0 3]]`.

## The fixpoint argument

Forward by induction on the C-side derivation.  Backward by strong induction on
fuel: a call re-enters a definition body, which is not a subterm, but it runs
at strictly smaller fuel, so the fuel measure supplies its induction hypothesis
— uniformly, for self- and mutual recursion alike.
-/

-- ---------------------------------------------------------------------------
-- Syntax and compilation
-- ---------------------------------------------------------------------------

/-- Terms with calls into a definition table. -/
inductive RTerm
  | nil  : RTerm
  | blk  : Term → RTerm → RTerm
  | call : Nat → RTerm → RTerm
  | ifte : RTerm → RTerm → RTerm → RTerm
  deriving Repr

/-- Axis, in the core `[B S]`, of the battery with its first `i` arms dropped. -/
def tailAx : Nat → Nat
  | 0     => 2
  | i + 1 => 2 * tailAx i + 1

/-- Axis, in the core `[B S]`, of arm `i`. -/
def armAx (i : Nat) : Nat := 2 * tailAx i

/-- Run a call-free block on the stack, keeping the battery:
    `[[0 2] [7 [0 3] Λ_N(t)]]`. -/
def blkF (t : Term) : Noun :=
  cell (cell (atom 0) (atom 2)) (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT t)))

/-- Call arm `i`: `[9 armAx(i) 0 1]`. -/
def callF (i : Nat) : Noun :=
  cell (atom 9) (cell (atom (armAx i)) (cell (atom 0) (atom 1)))

/-- Pop the flag, keeping the battery: `[[0 2] 0 7]`. -/
def popF : Noun := cell (cell (atom 0) (atom 2)) (cell (atom 0) (atom 7))

/-- The compiler, against the core `[B S]`. -/
def NR : RTerm → Noun
  | .nil          => cell (atom 0) (atom 1)
  | .blk t k      => cell (atom 7) (cell (blkF t) (NR k))
  | .call i k     => cell (atom 7) (cell (callF i) (NR k))
  | .ifte q₁ q₂ k =>
      cell (atom 7) (cell
        (cell (atom 6) (cell (cell (atom 0) (atom 6))
          (cell (cell (atom 7) (cell popF (NR q₁)))
                (cell (atom 7) (cell popF (NR q₂))))))
        (NR k))

/-- The branch schema of `ifte`, without its continuation. -/
def NRifte (q₁ q₂ : RTerm) : Noun :=
  cell (atom 6) (cell (cell (atom 0) (atom 6))
    (cell (cell (atom 7) (cell popF (NR q₁))) (cell (atom 7) (cell popF (NR q₂)))))

/-- The multi-armed battery of a definition table. -/
def battery : List RTerm → Noun
  | []      => atom 0
  | d :: ds => cell (NR d) (battery ds)

/-- Definition `i` of the table, if there is one. -/
def armOf : List RTerm → Nat → Option RTerm
  | [],      _     => none
  | d :: _,  0     => some d
  | _ :: ds, i + 1 => armOf ds i

/-- A whole program: pin the battery, run `main` against `[B S]`, unload `S'`.
    `[7 [[1 B] 0 1] [7 NR(main) 0 3]]` -/
def progF (D : List RTerm) (m : RTerm) : Noun :=
  cell (atom 7) (cell (cell (cell (atom 1) (battery D)) (cell (atom 0) (atom 1)))
    (cell (atom 7) (cell (NR m) (cell (atom 0) (atom 3)))))

/-- The Nock side returns the core `[B S']`, not the bare stack. -/
def wrapB (B : Noun) : Outcome → Outcome
  | .val S => .val (cell B S)
  | .exit  => .exit

-- ---------------------------------------------------------------------------
-- The C side
-- ---------------------------------------------------------------------------

/-- Big-step semantics of the C side: a call runs the callee's body to
    completion, then the continuation.  Divergence is absence of derivation. -/
inductive REval (D : List RTerm) : RTerm → Noun → Outcome → Prop where
  | nil {S} : REval D .nil S (.val S)

  | blk {t k S S' o} :
      CEval t S (.val S') → REval D k S' o → REval D (.blk t k) S o
  | blk_crash {t k S} :
      CEval t S .exit → REval D (.blk t k) S .exit

  | call {i k d S S' o} :
      armOf D i = some d → REval D d S (.val S') → REval D k S' o →
      REval D (.call i k) S o
  | call_crash {i k d S} :
      armOf D i = some d → REval D d S .exit → REval D (.call i k) S .exit
  | call_undef {i k S} :
      armOf D i = none → REval D (.call i k) S .exit

  | ifte_then {q₁ q₂ k r T o} :
      REval D q₁ r (.val T) → REval D k T o →
      REval D (.ifte q₁ q₂ k) (cell (atom 0) r) o
  | ifte_then_crash {q₁ q₂ k r} :
      REval D q₁ r .exit → REval D (.ifte q₁ q₂ k) (cell (atom 0) r) .exit
  | ifte_else {q₁ q₂ k r T o} :
      REval D q₂ r (.val T) → REval D k T o →
      REval D (.ifte q₁ q₂ k) (cell (atom 1) r) o
  | ifte_else_crash {q₁ q₂ k r} :
      REval D q₂ r .exit → REval D (.ifte q₁ q₂ k) (cell (atom 1) r) .exit
  | ifte_nonloob {q₁ q₂ k f r} :
      f ≠ atom 0 → f ≠ atom 1 → REval D (.ifte q₁ q₂ k) (cell f r) .exit
  | ifte_atom {q₁ q₂ k n} :
      REval D (.ifte q₁ q₂ k) (atom n) .exit

/-- C-side divergence. -/
def RDiverges (D : List RTerm) (t : RTerm) (S : Noun) : Prop := ∀ o, ¬ REval D t S o

-- ---------------------------------------------------------------------------
-- Battery axes
-- ---------------------------------------------------------------------------

private theorem fasO_dbl (n : Nat) (b : Noun) :
    fasO (atom (2 * (n + 2))) b =
      (match fasO (atom (n + 2)) b with | some (cell hd _) => some hd | _ => none) := by
  have h1 : 2 * (n + 2) = 2 * n + 4 := by omega
  have h2 : (2 * n + 4) / 2 = n + 2 := by omega
  cases h : fasO (atom (n + 2)) b with
  | none => rw [h1]; simp only [fasO, h2, h]
  | some v =>
    cases v with
    | atom m => rw [h1]; simp only [fasO, h2, h]
    | cell hd tl => exact fasO_rec_even n b hd tl h

private theorem fasO_dbl1 (n : Nat) (b : Noun) :
    fasO (atom (2 * (n + 2) + 1)) b =
      (match fasO (atom (n + 2)) b with | some (cell _ tl) => some tl | _ => none) := by
  have h1 : 2 * (n + 2) + 1 = 2 * n + 5 := by omega
  have h2 : (2 * n + 5) / 2 = n + 2 := by omega
  cases h : fasO (atom (n + 2)) b with
  | none => rw [h1]; simp only [fasO, h2, h]
  | some v =>
    cases v with
    | atom m => rw [h1]; simp only [fasO, h2, h]
    | cell hd tl => exact fasO_rec_odd n b hd tl h

/-- The battery with its first `i` arms dropped, if there are at least `i`. -/
private def batDrop : Nat → List RTerm → Option Noun
  | 0,     D       => some (battery D)
  | _ + 1, []      => none
  | i + 1, _ :: ds => batDrop i ds

private theorem batDrop_succ : ∀ (i : Nat) (D : List RTerm),
    batDrop (i + 1) D =
      (match batDrop i D with | some (cell _ tl) => some tl | _ => none)
  | 0,     []      => rfl
  | 0,     _ :: _  => rfl
  | _ + 1, []      => rfl
  | i + 1, _ :: ds => batDrop_succ i ds

private theorem batDrop_head : ∀ (i : Nat) (D : List RTerm),
    (match batDrop i D with | some (cell hd _) => some hd | _ => none) =
      (armOf D i).map NR
  | 0,     []      => rfl
  | 0,     _ :: _  => rfl
  | _ + 1, []      => rfl
  | i + 1, _ :: ds => batDrop_head i ds

private theorem two_le_tailAx : ∀ i, 2 ≤ tailAx i
  | 0     => Nat.le_refl 2
  | i + 1 => by
    have := two_le_tailAx i
    show 2 ≤ 2 * tailAx i + 1
    omega

private theorem fasO_tailAx (D : List RTerm) (S : Noun) : ∀ i : Nat,
    fasO (atom (tailAx i)) (cell (battery D) S) = batDrop i D
  | 0     => fasO_head _ _
  | i + 1 => by
    obtain ⟨n, hn⟩ : ∃ n, tailAx i = n + 2 :=
      ⟨tailAx i - 2, by have := two_le_tailAx i; omega⟩
    have ih := fasO_tailAx D S i
    rw [hn] at ih
    show fasO (atom (2 * tailAx i + 1)) _ = _
    rw [hn, fasO_dbl1, ih, batDrop_succ]

/-- Arm `i` of the core `[B S]` is the compiled definition `i`, or nothing. -/
theorem fasO_armAx (D : List RTerm) (S : Noun) (i : Nat) :
    fasO (atom (armAx i)) (cell (battery D) S) = (armOf D i).map NR := by
  obtain ⟨n, hn⟩ : ∃ n, tailAx i = n + 2 :=
    ⟨tailAx i - 2, by have := two_le_tailAx i; omega⟩
  have ht := fasO_tailAx D S i
  rw [hn] at ht
  show fasO (atom (2 * tailAx i)) _ = _
  rw [hn, fasO_dbl, ht, batDrop_head]

private theorem arm_some {D : List RTerm} {S : Noun} {i : Nat} {d : RTerm}
    (hl : armOf D i = some d) :
    fasO (atom (armAx i)) (cell (battery D) S) = some (NR d) := by
  have h := fasO_armAx D S i
  rw [hl] at h
  exact h

private theorem arm_none {D : List RTerm} {S : Noun} {i : Nat}
    (hl : armOf D i = none) :
    fasO (atom (armAx i)) (cell (battery D) S) = none := by
  have h := fasO_armAx D S i
  rw [hl] at h
  exact h

-- ---------------------------------------------------------------------------
-- Plumbing
-- ---------------------------------------------------------------------------

private theorem no_val_exit {s f v} (hv : NockEval s f (.val v))
    (he : NockEval s f .exit) : False := by
  have := NockEval.deterministic hv he; simp at this

private theorem det_val {s f} {u v : Noun} (h1 : NockEval s f (.val u))
    (h2 : NockEval s f (.val v)) : u = v := by
  have := NockEval.deterministic h1 h2; simpa using this

private theorem nF_det {k : Nat} {S f : Noun} {x y : Outcome}
    (hk : nockF k S f = some x) (hy : NockEval S f y) : x = y :=
  NockEval.deterministic (nockF_sound k hk) hy

private theorem pop_eval (B f r : Noun) :
    NockEval (cell B (cell f r)) popF (.val (cell B r)) :=
  NockEval.autocons (NockEval.op0 (fasO_head B (cell f r))) (NockEval.op0 (fasO_seven B f r))

private theorem blk_eval {B S : Noun} {t : Term} {x : Outcome} (hc : CEval t S x) :
    NockEval (cell B S) (blkF t) (wrapB B x) := by
  have hN : NockEval (cell B S) (cell (atom 7) (cell (cell (atom 0) (atom 3)) (NT t))) x :=
    NockEval.op7 (NockEval.op0 (fasO_tail B S)) (ceval_sound hc)
  cases x with
  | val S' => exact NockEval.autocons (NockEval.op0 (fasO_head B S)) hN
  | exit   => exact NockEval.autocons_crashR (NockEval.op0 (fasO_head B S)) hN

private theorem blk_inv {B S : Noun} {t : Term} {y : Outcome}
    (h : NockEval (cell B S) (blkF t) y) : ∃ x, CEval t S x ∧ y = wrapB B x := by
  have h2 : NockEval (cell B S) (cell (atom 0) (atom 2)) (.val B) :=
    NockEval.op0 (fasO_head B S)
  have h3 : NockEval (cell B S) (cell (atom 0) (atom 3)) (.val S) :=
    NockEval.op0 (fasO_tail B S)
  cases h with
  | crash_malformed hm => simp [Malformed, blkF] at hm
  | autocons ha hb =>
    have := det_val ha h2; subst this
    cases hb with
    | op7 hc hd =>
      have := det_val hc h3; subst this
      exact ⟨_, nockeval_complete hd, rfl⟩
  | autocons_crashL ha => exact (no_val_exit h2 ha).elim
  | autocons_crashR _ hb =>
    cases hb with
    | crash_malformed hm => simp [Malformed] at hm
    | op7_crash hc => exact (no_val_exit h3 hc).elim
    | op7 hc hd =>
      have := det_val hc h3; subst this
      exact ⟨_, nockeval_complete hd, rfl⟩

-- ---------------------------------------------------------------------------
-- Forward: REval → NockEval
-- ---------------------------------------------------------------------------

/-- **Forward simulation.**  Every C derivation is matched by a Nock derivation
    of the compiled term against the core, with the battery carried through. -/
theorem reval_sound {D : List RTerm} {t : RTerm} {S : Noun} {o : Outcome}
    (h : REval D t S o) :
    NockEval (cell (battery D) S) (NR t) (wrapB (battery D) o) := by
  induction h with
  | nil => exact NockEval.op0 (fasO_one _)
  | blk hc _ ih => exact NockEval.op7 (blk_eval hc) ih
  | blk_crash hc => exact NockEval.op7_crash (blk_eval hc)
  | call hl _ _ ih₁ ih₂ =>
    exact NockEval.op7 (NockEval.op9 (NockEval.op0 (fasO_one _)) (arm_some hl) ih₁) ih₂
  | call_crash hl _ ih₁ =>
    exact NockEval.op7_crash (NockEval.op9 (NockEval.op0 (fasO_one _)) (arm_some hl) ih₁)
  | call_undef hl =>
    exact NockEval.op7_crash (NockEval.op9_badaxis (NockEval.op0 (fasO_one _)) (arm_none hl))
  | ifte_then _ _ ih₁ ih₂ =>
    exact NockEval.op7
      (NockEval.op6_then (NockEval.op0 (fasO_six _ _ _))
        (NockEval.op7 (pop_eval _ _ _) ih₁)) ih₂
  | ifte_then_crash _ ih₁ =>
    exact NockEval.op7_crash
      (NockEval.op6_then (NockEval.op0 (fasO_six _ _ _))
        (NockEval.op7 (pop_eval _ _ _) ih₁))
  | ifte_else _ _ ih₁ ih₂ =>
    exact NockEval.op7
      (NockEval.op6_else (NockEval.op0 (fasO_six _ _ _))
        (NockEval.op7 (pop_eval _ _ _) ih₁)) ih₂
  | ifte_else_crash _ ih₁ =>
    exact NockEval.op7_crash
      (NockEval.op6_else (NockEval.op0 (fasO_six _ _ _))
        (NockEval.op7 (pop_eval _ _ _) ih₁))
  | ifte_nonloob hne0 hne1 =>
    exact NockEval.op7_crash
      (NockEval.op6_nonloob (NockEval.op0 (fasO_six _ _ _)) hne0 hne1)
  | ifte_atom =>
    exact NockEval.op7_crash
      (NockEval.op6_crash (NockEval.op0_crash (fasO_six_atomtail _ _)))

-- ---------------------------------------------------------------------------
-- Backward: by strong induction on fuel
-- ---------------------------------------------------------------------------

private theorem rF_op7 (k : Nat) (S f g : Noun) :
    nockF (k+1) S (cell (atom 7) (cell f g)) =
      (match nockF k S f with
       | none => none | some .exit => some .exit
       | some (.val r) => nockF k r g) := rfl

private theorem rF_op9 (k : Nat) (S bx c : Noun) :
    nockF (k+1) S (cell (atom 9) (cell bx c)) =
      (match nockF k S c with
       | none => none | some .exit => some .exit
       | some (.val core) =>
         match fasO bx core with
         | some arm => nockF k core arm
         | none => some .exit) := rfl

private theorem rF_op6 (k : Nat) (S b c d : Noun) :
    nockF (k+1) S (cell (atom 6) (cell b (cell c d))) =
      (match nockF k S b with
       | none => none | some .exit => some .exit
       | some (.val (atom 0)) => nockF k S c
       | some (.val (atom 1)) => nockF k S d
       | some (.val _) => some .exit) := rfl

private theorem inv_op7 {k : Nat} {X A C : Noun} {o : Outcome}
    (h : nockF k X (cell (atom 7) (cell A C)) = some o) :
    ∃ j, j < k ∧ ((nockF j X A = some .exit ∧ o = .exit) ∨
      ∃ r, nockF j X A = some (.val r) ∧ nockF j r C = some o) := by
  cases k with
  | zero => simp [nockF] at h
  | succ j =>
    rw [rF_op7] at h
    refine ⟨j, by omega, ?_⟩
    cases hA : nockF j X A with
    | none => rw [hA] at h; simp at h
    | some x =>
      cases x with
      | exit =>
        rw [hA] at h; dsimp only at h
        exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
      | val r =>
        rw [hA] at h; dsimp only at h
        exact Or.inr ⟨r, rfl, h⟩

private theorem inv_op9 {k : Nat} {X ax c : Noun} {o : Outcome}
    (h : nockF k X (cell (atom 9) (cell ax c)) = some o) :
    ∃ j, j < k ∧ ((nockF j X c = some .exit ∧ o = .exit) ∨
      ∃ core, nockF j X c = some (.val core) ∧
        ((fasO ax core = none ∧ o = .exit) ∨
         ∃ arm, fasO ax core = some arm ∧ nockF j core arm = some o)) := by
  cases k with
  | zero => simp [nockF] at h
  | succ j =>
    rw [rF_op9] at h
    refine ⟨j, by omega, ?_⟩
    cases hc : nockF j X c with
    | none => rw [hc] at h; simp at h
    | some x =>
      cases x with
      | exit =>
        rw [hc] at h; dsimp only at h
        exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
      | val core =>
        rw [hc] at h; dsimp only at h
        refine Or.inr ⟨core, rfl, ?_⟩
        cases hf : fasO ax core with
        | none =>
          rw [hf] at h; dsimp only at h
          exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
        | some arm =>
          rw [hf] at h; dsimp only at h
          exact Or.inr ⟨arm, rfl, h⟩

private theorem inv_op6 {k : Nat} {X b c d : Noun} {o : Outcome}
    (h : nockF k X (cell (atom 6) (cell b (cell c d))) = some o) :
    ∃ j, j < k ∧ ((nockF j X b = some .exit ∧ o = .exit) ∨
      (nockF j X b = some (.val (atom 0)) ∧ nockF j X c = some o) ∨
      (nockF j X b = some (.val (atom 1)) ∧ nockF j X d = some o) ∨
      (∃ r, nockF j X b = some (.val r) ∧ r ≠ atom 0 ∧ r ≠ atom 1 ∧ o = .exit)) := by
  cases k with
  | zero => simp [nockF] at h
  | succ j =>
    rw [rF_op6] at h
    refine ⟨j, by omega, ?_⟩
    cases hb : nockF j X b with
    | none => rw [hb] at h; simp at h
    | some x =>
      cases x with
      | exit =>
        rw [hb] at h; dsimp only at h
        exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
      | val r =>
        rw [hb] at h
        match r with
        | atom 0 =>
          dsimp only at h
          exact Or.inr (Or.inl ⟨rfl, h⟩)
        | atom 1 =>
          dsimp only at h
          exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
        | atom (n + 2) =>
          exact Or.inr (Or.inr (Or.inr ⟨atom (n + 2), rfl,
            (fun e => by cases e), (fun e => by cases e), (Option.some.inj h).symm⟩))
        | cell x z =>
          exact Or.inr (Or.inr (Or.inr ⟨cell x z, rfl,
            (fun e => by cases e), (fun e => by cases e), (Option.some.inj h).symm⟩))

/-- The induction hypothesis of the fuel induction, at every fuel below `k`. -/
private def BackIH (D : List RTerm) (k : Nat) : Prop :=
  ∀ m, m < k → ∀ {t : RTerm} {S : Noun} {o : Outcome},
    nockF m (cell (battery D) S) (NR t) = some o →
      ∃ o', REval D t S o' ∧ o = wrapB (battery D) o'

/-- A call either finds no arm (and crashes), or runs the callee's body. -/
private theorem call_back {D : List RTerm} {j i : Nat} {S : Noun} {y : Outcome}
    (ih : BackIH D j) (h : nockF j (cell (battery D) S) (callF i) = some y) :
    (armOf D i = none ∧ y = .exit) ∨
    ∃ d, armOf D i = some d ∧ ∃ o₁, REval D d S o₁ ∧ y = wrapB (battery D) o₁ := by
  obtain ⟨j', hj', hc⟩ :=
    inv_op9 (ax := atom (armAx i)) (c := cell (atom 0) (atom 1)) h
  have h01 : NockEval (cell (battery D) S) (cell (atom 0) (atom 1))
      (.val (cell (battery D) S)) := NockEval.op0 (fasO_one _)
  rcases hc with ⟨he, -⟩ | ⟨core, hv, hcase⟩
  · have := nF_det he h01; cases this
  · have := nF_det hv h01; cases this
    have harm := fasO_armAx D S i
    rcases hcase with ⟨hn, rfl⟩ | ⟨arm, ha, hrun⟩
    · refine Or.inl ⟨?_, rfl⟩
      rw [hn] at harm
      cases hl : armOf D i with
      | none => rfl
      | some d => rw [hl] at harm; cases harm
    · refine Or.inr ?_
      rw [ha] at harm
      cases hl : armOf D i with
      | none => rw [hl] at harm; cases harm
      | some d =>
        rw [hl] at harm
        cases harm
        obtain ⟨o₁, hr, hy⟩ := ih j' hj' hrun
        exact ⟨d, rfl, o₁, hr, hy⟩

/-- A conditional either crashes on its flag, or runs one branch on the rest. -/
private theorem ifte_back {D : List RTerm} {j : Nat} {q₁ q₂ : RTerm} {S : Noun}
    {y : Outcome} (ih : BackIH D j)
    (h : nockF j (cell (battery D) S) (NRifte q₁ q₂) = some y) :
    (∃ n, S = atom n ∧ y = .exit) ∨
    (∃ r o₁, S = cell (atom 0) r ∧ REval D q₁ r o₁ ∧ y = wrapB (battery D) o₁) ∨
    (∃ r o₁, S = cell (atom 1) r ∧ REval D q₂ r o₁ ∧ y = wrapB (battery D) o₁) ∨
    (∃ f r, S = cell f r ∧ f ≠ atom 0 ∧ f ≠ atom 1 ∧ y = .exit) := by
  obtain ⟨j', hj', hc⟩ :=
    inv_op6 (b := cell (atom 0) (atom 6)) (c := cell (atom 7) (cell popF (NR q₁)))
      (d := cell (atom 7) (cell popF (NR q₂))) h
  have branch : ∀ {q : RTerm} {f r : Noun},
      nockF j' (cell (battery D) (cell f r)) (cell (atom 7) (cell popF (NR q))) = some y →
      ∃ o₁, REval D q r o₁ ∧ y = wrapB (battery D) o₁ := by
    intro q f r hb
    obtain ⟨j'', hj'', hp⟩ := inv_op7 hb
    rcases hp with ⟨hpop, -⟩ | ⟨r', hpop, hrun⟩
    · have := nF_det hpop (pop_eval (battery D) f r); cases this
    · have := nF_det hpop (pop_eval (battery D) f r); cases this
      exact ih j'' (by omega) hrun
  rcases hc with ⟨ht, rfl⟩ | ⟨ht, hb⟩ | ⟨ht, hb⟩ | ⟨v, ht, hne0, hne1, rfl⟩
  · cases S with
    | atom n => exact Or.inl ⟨n, rfl, rfl⟩
    | cell f r =>
      have := nF_det ht (NockEval.op0 (fasO_six (battery D) f r)); cases this
  · cases S with
    | atom n =>
      have := nF_det ht (NockEval.op0_crash (fasO_six_atomtail (battery D) n)); cases this
    | cell f r =>
      have := nF_det ht (NockEval.op0 (fasO_six (battery D) f r)); cases this
      obtain ⟨o₁, hq, hy⟩ := branch hb
      exact Or.inr (Or.inl ⟨r, o₁, rfl, hq, hy⟩)
  · cases S with
    | atom n =>
      have := nF_det ht (NockEval.op0_crash (fasO_six_atomtail (battery D) n)); cases this
    | cell f r =>
      have := nF_det ht (NockEval.op0 (fasO_six (battery D) f r)); cases this
      obtain ⟨o₁, hq, hy⟩ := branch hb
      exact Or.inr (Or.inr (Or.inl ⟨r, o₁, rfl, hq, hy⟩))
  · cases S with
    | atom n =>
      have := nF_det ht (NockEval.op0_crash (fasO_six_atomtail (battery D) n)); cases this
    | cell f r =>
      have := nF_det ht (NockEval.op0 (fasO_six (battery D) f r)); cases this
      exact Or.inr (Or.inr (Or.inr ⟨_, r, rfl, hne0, hne1, rfl⟩))

/-- The fuel induction.  Every recursive obligation — a continuation, a branch,
    or a callee's body, which need not be a subterm — appears in `nockF`'s
    computation at strictly smaller fuel. -/
theorem rback_fuel (D : List RTerm) : ∀ k : Nat, ∀ {t : RTerm} {S : Noun} {o : Outcome},
    nockF k (cell (battery D) S) (NR t) = some o →
      ∃ o', REval D t S o' ∧ o = wrapB (battery D) o' := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro t S o h
  match t with
  | .nil =>
    exact ⟨.val S, REval.nil, nF_det h (NockEval.op0 (fasO_one (cell (battery D) S)))⟩
  | .blk t' c =>
    obtain ⟨j, hj, hcase⟩ := inv_op7 (A := blkF t') (C := NR c) h
    rcases hcase with ⟨hA, rfl⟩ | ⟨r, hA, hC⟩
    · obtain ⟨x, hx, hxe⟩ := blk_inv (nockF_sound j hA)
      cases x with
      | val _ => cases hxe
      | exit  => exact ⟨.exit, REval.blk_crash hx, rfl⟩
    · obtain ⟨x, hx, hxe⟩ := blk_inv (nockF_sound j hA)
      cases x with
      | exit => cases hxe
      | val S' =>
        cases hxe
        obtain ⟨o', hk, ho⟩ := ih j hj hC
        exact ⟨o', REval.blk hx hk, ho⟩
  | .call i c =>
    obtain ⟨j, hj, hcase⟩ := inv_op7 (A := callF i) (C := NR c) h
    have ihj : BackIH D j := fun m hm => ih m (by omega)
    rcases hcase with ⟨hA, rfl⟩ | ⟨r, hA, hC⟩
    · rcases call_back ihj hA with ⟨hl, -⟩ | ⟨d, hl, o₁, hr, hy⟩
      · exact ⟨.exit, REval.call_undef hl, rfl⟩
      · cases o₁ with
        | val _ => cases hy
        | exit  => exact ⟨.exit, REval.call_crash hl hr, rfl⟩
    · rcases call_back ihj hA with ⟨-, hy⟩ | ⟨d, hl, o₁, hr, hy⟩
      · cases hy
      · cases o₁ with
        | exit => cases hy
        | val S' =>
          cases hy
          obtain ⟨o', hk, ho⟩ := ih j hj hC
          exact ⟨o', REval.call hl hr hk, ho⟩
  | .ifte q₁ q₂ c =>
    obtain ⟨j, hj, hcase⟩ := inv_op7 (A := NRifte q₁ q₂) (C := NR c) h
    have ihj : BackIH D j := fun m hm => ih m (by omega)
    rcases hcase with ⟨hA, rfl⟩ | ⟨r, hA, hC⟩
    · rcases ifte_back ihj hA with
        ⟨n, rfl, -⟩ | ⟨r, o₁, rfl, hq, hy⟩ | ⟨r, o₁, rfl, hq, hy⟩ | ⟨f, r, rfl, hne0, hne1, -⟩
      · exact ⟨.exit, REval.ifte_atom, rfl⟩
      · cases o₁ with
        | val _ => cases hy
        | exit  => exact ⟨.exit, REval.ifte_then_crash hq, rfl⟩
      · cases o₁ with
        | val _ => cases hy
        | exit  => exact ⟨.exit, REval.ifte_else_crash hq, rfl⟩
      · exact ⟨.exit, REval.ifte_nonloob hne0 hne1, rfl⟩
    · rcases ifte_back ihj hA with
        ⟨n, rfl, hy⟩ | ⟨r', o₁, rfl, hq, hy⟩ | ⟨r', o₁, rfl, hq, hy⟩ | ⟨f, r', rfl, -, -, hy⟩
      · cases hy
      · cases o₁ with
        | exit => cases hy
        | val T =>
          cases hy
          obtain ⟨o', hk, ho⟩ := ih j hj hC
          exact ⟨o', REval.ifte_then hq hk, ho⟩
      · cases o₁ with
        | exit => cases hy
        | val T =>
          cases hy
          obtain ⟨o', hk, ho⟩ := ih j hj hC
          exact ⟨o', REval.ifte_else hq hk, ho⟩
      · cases hy

-- ---------------------------------------------------------------------------
-- The theorems
-- ---------------------------------------------------------------------------

/-- **Composition with named definitions.**  Against the core `[B S]`, the
    compiled term and the C semantics agree on values (with the battery carried
    through) and on crashes, for every definition table — self- and mutually
    recursive alike. -/
theorem rcomposition (D : List RTerm) (t : RTerm) (S : Noun) (o : Outcome) :
    NockEval (cell (battery D) S) (NR t) o ↔
      ∃ o', REval D t S o' ∧ o = wrapB (battery D) o' := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := nockF_complete h
    exact rback_fuel D k hk
  · rintro ⟨o', h, rfl⟩
    exact reval_sound h

/-- ... and on divergence. -/
theorem rcomposition_diverges (D : List RTerm) (t : RTerm) (S : Noun) :
    Diverges (cell (battery D) S) (NR t) ↔ RDiverges D t S := by
  constructor
  · intro hd o h
    exact hd _ (reval_sound h)
  · intro hr o h
    obtain ⟨o', h', -⟩ := (rcomposition D t S o).1 h
    exact hr o' h'

/-- **The program theorem.**  A whole program — battery pinned, `main` run,
    stack unloaded — agrees exactly with the C semantics of `main`. -/
theorem program_term (D : List RTerm) (m : RTerm) (S : Noun) (o : Outcome) :
    NockEval S (progF D m) o ↔ REval D m S o := by
  have hload : NockEval S (cell (cell (atom 1) (battery D)) (cell (atom 0) (atom 1)))
      (.val (cell (battery D) S)) :=
    NockEval.autocons NockEval.op1 (NockEval.op0 (fasO_one S))
  constructor
  · intro h
    cases h with
    | crash_malformed hm => simp [Malformed, progF] at hm
    | op7_crash hl => exact (no_val_exit hload hl).elim
    | op7 hl hr =>
      have := det_val hl hload; subst this
      cases hr with
      | crash_malformed hm => simp [Malformed] at hm
      | op7_crash hn =>
        obtain ⟨o', h', ho⟩ := (rcomposition D m S .exit).1 hn
        cases o' with
        | val _ => cases ho
        | exit  => exact h'
      | op7 hn hu =>
        obtain ⟨o', h', ho⟩ := (rcomposition D m S _).1 hn
        cases o' with
        | exit => cases ho
        | val S' =>
          cases ho
          have := NockEval.deterministic hu (NockEval.op0 (fasO_tail (battery D) S'))
          subst this
          exact h'
  · intro h
    have hf := reval_sound h
    refine NockEval.op7 hload ?_
    cases o with
    | val S' => exact NockEval.op7 hf (NockEval.op0 (fasO_tail _ _))
    | exit   => exact NockEval.op7_crash hf

theorem program_diverges (D : List RTerm) (m : RTerm) (S : Noun) :
    Diverges S (progF D m) ↔ RDiverges D m S := by
  simp only [Diverges, RDiverges, program_term]

/-- A call-free block is exactly a Class D term: the extension is conservative. -/
theorem reval_blk_nil (D : List RTerm) (t : Term) (S : Noun) (o : Outcome) :
    REval D (.blk t .nil) S o ↔ CEval t S o := by
  constructor
  · intro h
    cases h with
    | blk hc hk => cases hk; exact hc
    | blk_crash hc => exact hc
  · intro h
    cases o with
    | val S' => exact REval.blk h REval.nil
    | exit   => exact REval.blk_crash h

theorem program_ofTerm (D : List RTerm) (t : Term) (S : Noun) (o : Outcome) :
    NockEval S (progF D (.blk t .nil)) o ↔ CEval t S o :=
  (program_term D _ S o).trans (reval_blk_nil D t S o)

-- ---------------------------------------------------------------------------
-- Examples
-- ---------------------------------------------------------------------------

-- Self-recursion: definition 0 pops a flag; on 0 it calls itself, on 1 it stops.
-- On [0 [0 [1 r]]] the compiled program returns r.
example (r : Noun) :
    NockEval (cell (atom 0) (cell (atom 0) (cell (atom 1) r)))
      (progF [.ifte (.call 0 .nil) .nil .nil] (.call 0 .nil)) (.val r) := by
  rw [program_term]
  have d1 : REval [.ifte (.call 0 .nil) .nil .nil] (.ifte (.call 0 .nil) .nil .nil)
      (cell (atom 1) r) (.val r) := REval.ifte_else REval.nil REval.nil
  have d2 : REval [.ifte (.call 0 .nil) .nil .nil] (.ifte (.call 0 .nil) .nil .nil)
      (cell (atom 0) (cell (atom 1) r)) (.val r) :=
    REval.ifte_then (REval.call rfl d1 REval.nil) REval.nil
  have d3 : REval [.ifte (.call 0 .nil) .nil .nil] (.ifte (.call 0 .nil) .nil .nil)
      (cell (atom 0) (cell (atom 0) (cell (atom 1) r))) (.val r) :=
    REval.ifte_then (REval.call rfl d2 REval.nil) REval.nil
  exact REval.call rfl d3 REval.nil

-- Mutual recursion: definitions 0 and 1 each pop a flag and, on 0, call the other.
example (r : Noun) :
    NockEval (cell (atom 0) (cell (atom 0) (cell (atom 1) r)))
      (progF [.ifte (.call 1 .nil) .nil .nil, .ifte (.call 0 .nil) .nil .nil]
        (.call 0 .nil)) (.val r) := by
  rw [program_term]
  have d0 : REval [.ifte (.call 1 .nil) .nil .nil, .ifte (.call 0 .nil) .nil .nil]
      (.ifte (.call 1 .nil) .nil .nil) (cell (atom 1) r) (.val r) :=
    REval.ifte_else REval.nil REval.nil
  have d1 : REval [.ifte (.call 1 .nil) .nil .nil, .ifte (.call 0 .nil) .nil .nil]
      (.ifte (.call 0 .nil) .nil .nil) (cell (atom 0) (cell (atom 1) r)) (.val r) :=
    REval.ifte_then (REval.call rfl d0 REval.nil) REval.nil
  have d2 : REval [.ifte (.call 1 .nil) .nil .nil, .ifte (.call 0 .nil) .nil .nil]
      (.ifte (.call 1 .nil) .nil .nil) (cell (atom 0) (cell (atom 0) (cell (atom 1) r)))
      (.val r) :=
    REval.ifte_then (REval.call rfl d1 REval.nil) REval.nil
  exact REval.call rfl d2 REval.nil
