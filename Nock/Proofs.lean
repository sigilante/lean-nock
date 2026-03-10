import Nock.Basic
open Noun

/-!
# Nock Proofs

Theorems about the Nock 4K interpreter defined in `Nock.Basic`.
-/

-- Example: wut on an atom always returns 1
theorem wut_atom (n : Nat) : wut (atom n) = atom 1 := by
  simp [wut]

-- Example: wut on a cell always returns 0
theorem wut_cell (a b : Noun) : wut (cell a b) = atom 0 := by
  simp [wut]

-- Example: lus increments the atom
theorem lus_atom (n : Nat) : lus (atom n) = atom (1 + n) := by
  simp [lus]

-- Example: tis on equal nouns returns 0
theorem tis_refl (a : Noun) : tis (cell a a) = atom 0 := by
  simp [tis]
