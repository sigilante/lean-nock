import Nock.Basic
open Noun

/-!
# Nock Proofs

Theorems about the Nock 4K primitives defined in `Nock.Basic`.

Layer 1: the primitive operators (wut, lusO, tisN, fasO, haxO).
These are the foundation — every nock opcode proof reduces to these.

`lusO`, `fasO` and `haxO` are `Option`-valued: `none` is a Nock crash.
The recursion equations below are therefore stated with an explicit
`= some _` hypothesis on the sub-result rather than assuming success.
-/

-- ---------------------------------------------------------------------------
-- wut (?): cell/atom test
-- ---------------------------------------------------------------------------

theorem wut_atom (n : Nat) : wut (atom n) = atom 1 := by simp [wut]
theorem wut_cell (a b : Noun) : wut (cell a b) = atom 0 := by simp [wut]

-- ---------------------------------------------------------------------------
-- lusO (+): increment.  Crashes (none) on a cell.
-- ---------------------------------------------------------------------------

theorem lusO_atom (n : Nat) : lusO (atom n) = some (atom (1 + n)) := by simp [lusO]
theorem lusO_cell (a b : Noun) : lusO (cell a b) = none := by simp [lusO]

-- ---------------------------------------------------------------------------
-- tisN (=): equality test (Nock loobean: 0 = yes, 1 = no)
-- ---------------------------------------------------------------------------

theorem tisN_refl (a : Noun) : tisN a a = atom 0 := by simp [tisN]

theorem tisN_neq (a b : Noun) (h : a ≠ b) : tisN a b = atom 1 := by
  simp [tisN, h]

-- ---------------------------------------------------------------------------
-- fasO (/): tree address / slot
--
-- Three layers:
--   1. Base cases  (axes 1, 2, 3) — direct by definition
--   2. Recursion equations  — the Nock spec rules stated as theorems
--   3. Corollaries at axes 4–7 — the slots a two-level gate tree uses
-- ---------------------------------------------------------------------------

-- Layer 1: base cases
theorem fasO_one  (a : Noun) : fasO (atom 1) a = some a := by simp [fasO]
theorem fasO_head (a b : Noun) : fasO (atom 2) (cell a b) = some a := by simp [fasO]
theorem fasO_tail (a b : Noun) : fasO (atom 3) (cell a b) = some b := by simp [fasO]

-- Axis 0 always crashes.  The old `fas` could not state this: its axis-0
-- arm was `panic!`, which is `atom 0` inside Lean's logic.
theorem fasO_zero (a : Noun) : fasO (atom 0) a = none := by simp [fasO]

-- Layer 2: recursion equations  /[(2n) b]   = /[2 /[n b]]
--                               /[(2n+1) b] = /[3 /[n b]]
-- Conditional on the sub-result being a cell; when it is an atom, or the
-- sub-lookup itself crashes, `fasO` returns `none`.
theorem fasO_rec_even (n : Nat) (b a c : Noun)
    (h : fasO (atom (n + 2)) b = some (cell a c)) :
    fasO (atom (2 * (n + 2))) b = some a := by
  have h1 : 2 * (n + 2) = 2 * n + 4 := by omega
  have h2 : (2 * n + 4) / 2 = n + 2 := by omega
  have h3 : (2 * n + 4) % 2 = 0     := by omega
  rw [h1]; simp only [fasO, h2, h]; rw [if_pos h3]

theorem fasO_rec_odd (n : Nat) (b a c : Noun)
    (h : fasO (atom (n + 2)) b = some (cell a c)) :
    fasO (atom (2 * (n + 2) + 1)) b = some c := by
  have h1 : 2 * (n + 2) + 1 = 2 * n + 5 := by omega
  have h2 : (2 * n + 5) / 2 = n + 2     := by omega
  have h3 : ¬ (2 * n + 5) % 2 = 0       := by omega
  rw [h1]; simp only [fasO, h2, h]; rw [if_neg h3]

-- Layer 3: corollaries at axes 4–7 (the four slots of [[bat pay] [sam ctx]])
theorem fasO_four  (a b c : Noun) : fasO (atom 4) (cell (cell a b) c) = some a := by
  simp [fasO]
theorem fasO_five  (a b c : Noun) : fasO (atom 5) (cell (cell a b) c) = some b := by
  simp [fasO]
theorem fasO_six   (a b c : Noun) : fasO (atom 6) (cell a (cell b c)) = some b := by
  simp [fasO]
theorem fasO_seven (a b c : Noun) : fasO (atom 7) (cell a (cell b c)) = some c := by
  simp [fasO]

-- ---------------------------------------------------------------------------
-- haxO (#): tree update / edit-at-axis
--
-- Leo pseudocode:  a = axis/2,  b = axis%2,  parent = /[a old]
--   even (b=0):  new → head(parent);  return #(a, [new  /[(2a+1) old]], old)
--   odd  (b=1):  new → tail(parent);  return #(a, [/[(2a)   old] new], old)
-- Same structure as Lean: (n+2)/2 = a,  (n+2)%2 = b
--
-- The sibling lookup can crash, so the recursion equations carry a
-- `fasO ... = some sib` hypothesis.
-- ---------------------------------------------------------------------------

-- Base case: #[1 a b] = a
theorem haxO_one (a b : Noun) : haxO (atom 1) a b = some a := by simp [haxO]

-- Axis 0 always crashes.
theorem haxO_zero (a b : Noun) : haxO (atom 0) a b = none := by simp [haxO]

-- Recursion: #[2(a+1) b c] = #[(a+1) [b /[(2(a+1)+1) c]] c]   (even axis)
theorem haxO_rec_even (a : Nat) (b c sib : Noun)
    (h : fasO (atom (2 * (a + 1) + 1)) c = some sib) :
    haxO (atom (2 * (a + 1))) b c = haxO (atom (a + 1)) (cell b sib) c := by
  have h1 : 2 * (a + 1) = 2 * a + 2  := by omega
  have h2 : (2 * a + 2) / 2 = a + 1  := by omega
  have h3 : (2 * a + 2) % 2 = 0      := by omega
  -- rw [h1] rewrites 2*(a+1) to 2*a+2 everywhere, including 2*(a+1)+1 → 2*a+2+1
  rw [h1] at h ⊢; simp only [haxO, h2]; rw [if_pos h3]
  simp only [(by omega : (a + 1) + (a + 1) + 1 = 2 * a + 2 + 1), h]

-- Recursion: #[2(a+1)+1 b c] = #[(a+1) [/[(2(a+1)) c] b] c]  (odd axis)
theorem haxO_rec_odd (a : Nat) (b c sib : Noun)
    (h : fasO (atom (2 * (a + 1))) c = some sib) :
    haxO (atom (2 * (a + 1) + 1)) b c = haxO (atom (a + 1)) (cell sib b) c := by
  have h1 : 2 * (a + 1) + 1 = 2 * a + 3  := by omega
  have h2 : (2 * a + 3) / 2 = a + 1      := by omega
  have h3 : ¬ (2 * a + 3) % 2 = 0        := by omega
  -- rw [h1] rewrites 2*(a+1)+1 to 2*a+3; the RHS 2*(a+1) is untouched
  rw [h1]; simp only [haxO, h2]; rw [if_neg h3]
  simp only [(by omega : (a + 1) + (a + 1) = 2 * (a + 1)), h]

-- Derived: #[2 b c] = [b /[3 c]]   and   #[3 b c] = [/[2 c] b]
-- Stated conditionally on the sibling lookup succeeding.  `.get!` would
-- reintroduce the `Inhabited.default` hole this development exists to close.
theorem haxO_two (b c t : Noun) (h : fasO (atom 3) c = some t) :
    haxO (atom 2) b c = some (cell b t) := by
  rw [haxO_rec_even 0 b c t (by simpa using h), haxO_one]

theorem haxO_three (b c h2 : Noun) (h : fasO (atom 2) c = some h2) :
    haxO (atom 3) b c = some (cell h2 b) := by
  rw [haxO_rec_odd 0 b c h2 (by simpa using h), haxO_one]

-- Key corollary: replacing axis 6 (the sample slot) in a standard gate
-- #[6 b [bat [sam ctx]]] = [bat [b ctx]]
-- Unconditional: the gate shape guarantees both sibling lookups succeed.
-- This is the load-bearing lemma for every gate-call proof.
theorem haxO_six (b bat sam ctx : Noun) :
    haxO (atom 6) b (cell bat (cell sam ctx)) = some (cell bat (cell b ctx)) := by
  rw [haxO_rec_even 2 b _ ctx (fasO_seven bat sam ctx),
      haxO_rec_odd 0 _ _ bat (fasO_head bat (cell sam ctx)),
      haxO_one]

-- nock (*) reduction rules live in Nock.Eval as the NockEval inductive relation.
-- `partial def nock` is opaque to the kernel; use NockEval constructors for proofs.
