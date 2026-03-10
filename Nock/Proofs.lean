import Nock.Basic
open Noun

/-!
# Nock Proofs

Theorems about the Nock 4K interpreter defined in `Nock.Basic`.

Layer 1: the four primitive operators (wut, lus, tis, fas).
These are the foundation — every nock opcode proof reduces to these.
-/

-- ---------------------------------------------------------------------------
-- wut (?): cell/atom test
-- ---------------------------------------------------------------------------

theorem wut_atom (n : Nat) : wut (atom n) = atom 1 := by simp [wut]
theorem wut_cell (a b : Noun) : wut (cell a b) = atom 0 := by simp [wut]

-- ---------------------------------------------------------------------------
-- lus (+): increment
-- ---------------------------------------------------------------------------

theorem lus_atom (n : Nat) : lus (atom n) = atom (1 + n) := by simp [lus]

-- ---------------------------------------------------------------------------
-- tis (=): equality test (Nock loobean: 0 = yes, 1 = no)
-- ---------------------------------------------------------------------------

theorem tis_refl (a : Noun) : tis (cell a a) = atom 0 := by simp [tis]

theorem tis_neq (a b : Noun) (h : a ≠ b) : tis (cell a b) = atom 1 := by
  simp [tis, h]

-- ---------------------------------------------------------------------------
-- fas (/): tree address / slot
--
-- Three layers:
--   1. Base cases  (axes 1, 2, 3) — direct by definition
--   2. Recursion equations  — the Nock spec rules stated as theorems
--   3. Corollaries at axes 4–7 — the slots a two-level gate tree uses
-- ---------------------------------------------------------------------------

-- Layer 1: base cases
theorem fas_one  (a : Noun) : fas (atom 1) a = a := by simp [fas]
theorem fas_head (a b : Noun) : fas (atom 2) (cell a b) = a := by simp [fas]
theorem fas_tail (a b : Noun) : fas (atom 3) (cell a b) = b := by simp [fas]

-- Layer 2: recursion equations  /[(2n) b] = /[2 /[n b]]
--                                /[(2n+1) b] = /[3 /[n b]]
-- Stated conditionally on the sub-result being a cell — the panic arms at
-- different source positions are not definitionally equal, and valid Nock
-- never reaches them anyway.
theorem fas_rec_even (n : Nat) (b a c : Noun)
    (h : fas (atom (n + 2)) b = cell a c) :
    fas (atom (2 * (n + 2))) b = a := by
  have h1 : 2 * (n + 2) = 2 * n + 4 := by omega
  have h2 : (2 * n + 4) / 2 = n + 2 := by omega
  have h3 : (2 * n + 4) % 2 = 0     := by omega
  rw [h1]; simp only [fas, h2]; rw [if_pos h3, h]

theorem fas_rec_odd (n : Nat) (b a c : Noun)
    (h : fas (atom (n + 2)) b = cell a c) :
    fas (atom (2 * (n + 2) + 1)) b = c := by
  have h1 : 2 * (n + 2) + 1 = 2 * n + 5 := by omega
  have h2 : (2 * n + 5) / 2 = n + 2     := by omega
  have h3 : ¬ (2 * n + 5) % 2 = 0       := by omega
  rw [h1]; simp only [fas, h2]; rw [if_neg h3, h]

-- Layer 3: corollaries at axes 4–7 (the four slots of [[bat pay] [sam ctx]])
theorem fas_four  (a b c : Noun) : fas (atom 4) (cell (cell a b) c) = a := by simp [fas]
theorem fas_five  (a b c : Noun) : fas (atom 5) (cell (cell a b) c) = b := by simp [fas]
theorem fas_six   (a b c : Noun) : fas (atom 6) (cell a (cell b c)) = b := by simp [fas]
theorem fas_seven (a b c : Noun) : fas (atom 7) (cell a (cell b c)) = c := by simp [fas]

-- ---------------------------------------------------------------------------
-- hax (#): tree update / edit-at-axis
--
-- Leo pseudocode:  a = axis/2,  b = axis%2,  parent = /[a old]
--   even (b=0):  new → head(parent);  return #(a, [new  /[(2a+1) old]], old)
--   odd  (b=1):  new → tail(parent);  return #(a, [/[(2a)   old] new], old)
-- Same structure as Lean: (n+2)/2 = a,  (n+2)%2 = b
-- ---------------------------------------------------------------------------

-- Base case: #[1 a b] = a
theorem hax_one (a b : Noun) : hax (atom 1) a b = a := by simp [hax]

-- Recursion: #[2(a+1) b c] = #[(a+1) [b /[(2(a+1)+1) c]] c]   (even axis)
theorem hax_rec_even (a : Nat) (b c : Noun) :
    hax (atom (2 * (a + 1))) b c =
    hax (atom (a + 1)) (cell b (fas (atom (2 * (a + 1) + 1)) c)) c := by
  have h1 : 2 * (a + 1) = 2 * a + 2  := by omega
  have h2 : (2 * a + 2) / 2 = a + 1  := by omega
  have h3 : (2 * a + 2) % 2 = 0      := by omega
  -- rw [h1] rewrites 2*(a+1) to 2*a+2 everywhere, including 2*(a+1)+1 → 2*a+2+1
  rw [h1]; simp only [hax, h2]; rw [if_pos h3]
  simp only [(by omega : (a + 1) + (a + 1) + 1 = 2 * a + 2 + 1)]

-- Recursion: #[2(a+1)+1 b c] = #[(a+1) [/[(2(a+1)) c] b] c]  (odd axis)
theorem hax_rec_odd (a : Nat) (b c : Noun) :
    hax (atom (2 * (a + 1) + 1)) b c =
    hax (atom (a + 1)) (cell (fas (atom (2 * (a + 1))) c) b) c := by
  have h1 : 2 * (a + 1) + 1 = 2 * a + 3  := by omega
  have h2 : (2 * a + 3) / 2 = a + 1      := by omega
  have h3 : ¬ (2 * a + 3) % 2 = 0        := by omega
  -- rw [h1] rewrites 2*(a+1)+1 to 2*a+3; the RHS 2*(a+1) is untouched
  rw [h1]; simp only [hax, h2]; rw [if_neg h3]
  simp only [(by omega : (a + 1) + (a + 1) = 2 * (a + 1))]

-- Derived: #[2 b c] = [b /[3 c]]   and   #[3 b c] = [/[2 c] b]
theorem hax_two   (b c : Noun) : hax (atom 2) b c = cell b (fas (atom 3) c) := by
  rw [hax_rec_even 0, hax_one]
theorem hax_three (b c : Noun) : hax (atom 3) b c = cell (fas (atom 2) c) b := by
  rw [hax_rec_odd 0, hax_one]

-- Key corollary: replacing axis 6 (the sample slot) in a standard gate
-- #[6 b [bat [sam ctx]]] = [bat [b ctx]]
theorem hax_six (b bat sam ctx : Noun) :
    hax (atom 6) b (cell bat (cell sam ctx)) = cell bat (cell b ctx) := by
  rw [hax_rec_even 2, fas_seven, hax_rec_odd 0, fas_head, hax_one]

-- nock (*) reduction rules live in Nock.Eval as the NockEval inductive relation.
-- `partial def nock` is opaque to the kernel; use NockEval constructors for proofs.
