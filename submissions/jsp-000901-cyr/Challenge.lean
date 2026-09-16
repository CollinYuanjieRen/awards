/-
Comparator-style challenge module for JSP-000901 / Erdős Problem #1084 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
`Proof/Main.lean` (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

open Finset

namespace Erdos1084Challenge

/-- All pairwise distances are at least `1`. -/
def IsSeparated (A : Finset ℝ) : Prop := ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|

/-- The number of pairs of points of `A` at distance exactly `1`, counted as ordered pairs
`(x, x + 1)`. -/
noncomputable def unitPairs (A : Finset ℝ) : ℕ := ((A ×ˢ A).filter fun p => p.2 - p.1 = 1).card

/-- The one-dimensional contact number `f₁ n`: the largest number of unit pairs among separated
`n`-point sets of reals. -/
noncomputable def contactOne (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsSeparated A ∧ unitPairs A = m}

theorem contactOne_eq (n : ℕ) : contactOne n = n - 1 := by
  sorry

theorem unitPairs_le_of_isSeparated (A : Finset ℝ) (hA : IsSeparated A) :
    unitPairs A ≤ A.card - 1 := by
  sorry

theorem exists_isSeparated_unitPairs_eq (n : ℕ) :
    ∃ A : Finset ℝ, A.card = n ∧ IsSeparated A ∧ unitPairs A = n - 1 := by
  sorry

end Erdos1084Challenge
