import Mathlib

/-!
Frozen statement of the JSP-000539 / Erdős #664 target, against Mathlib only, with `sorry`.
NOT imported by the build; it freezes the statement for comparison with the proved roots.
The definitions are identical, up to line wrapping, to the public comparator challenge
`plby/lean-proofs: src/latest/ComparatorChallenges/ErdosProblems/Erdos664.lean`.
-/

open Finset

namespace Erdos664Target

def LinearFamily {ι α : Type*} [DecidableEq α] (A : ι → Finset α) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → #(A i ∩ A j) ≤ 1

def HitsAll {ι α : Type*} [Fintype ι] [DecidableEq α] (A : ι → Finset α) (B : Finset α) : Prop :=
  ∀ i, (B ∩ A i).Nonempty

def HasUniformTransversalBound (c : ℝ) (K : ℕ) : Prop :=
  ∀ n m : ℕ, ∀ A : Fin m → Finset (Fin n),
    (∀ i, c * Real.sqrt n < #(A i)) →
    LinearFamily A →
    ∃ B : Finset (Fin n), HitsAll A B ∧ ∀ i, #(B ∩ A i) ≤ K

/-- Negative resolution (Alon): for every constant `c < 1` there is no uniform bound. -/
theorem erdos_664 (c : ℝ) (hc : c < 1) : ¬ ∃ K : ℕ, HasUniformTransversalBound c K := by
  sorry

/-- The comparator-challenge instance `c = 2/5`. -/
theorem not_erdos_664 : ¬ ∃ K : ℕ, HasUniformTransversalBound (2 / 5 : ℝ) K := by
  sorry

end Erdos664Target
