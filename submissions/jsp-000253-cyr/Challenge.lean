/-
Comparator-style challenge module for JSP-000253 / Erdős Problem #301 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos301Challenge

/-- `A` admits a relation `1/a = 1/b₁ + ⋯ + 1/bₖ` with pairwise distinct elements of `A` (`k ≥ 1`). -/
def HasUnitSolution (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ B ⊆ A, a ∉ B ∧ B.Nonempty ∧ ((a : ℚ))⁻¹ = ∑ b ∈ B, ((b : ℚ))⁻¹

/-- `A` admits a relation `1/a = 1/b + ⋯ + 1/b` (`k ≥ 1` copies) with `a ≠ b` in `A`. -/
def HasRepeatedUnitSolution (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ k : ℕ, 0 < k ∧ ((a : ℚ))⁻¹ = k * ((b : ℚ))⁻¹

/-- The upper half `(N/2, N] ∩ ℕ`. -/
def upperHalf (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun n => N < 2 * n)

open Classical in
/-- `f(N)`: the largest size of a subset of `{1, …, N}` with no unit-fraction relation. -/
noncomputable def f (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => ¬ HasUnitSolution A)).sup Finset.card

theorem half_le_f (N : ℕ) : (N + 1) / 2 ≤ f N := by
  sorry

theorem not_hasUnitSolution_upperHalf (N : ℕ) : ¬ HasUnitSolution (upperHalf N) := by
  sorry

theorem card_upperHalf (N : ℕ) : (upperHalf N).card = (N + 1) / 2 := by
  sorry

theorem exists_dvd_of_half_lt_card (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (h : (N + 1) / 2 < A.card) : ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a ∣ b := by
  sorry

theorem card_le_half_of_not_hasRepeatedUnitSolution (N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (h : ¬ HasRepeatedUnitSolution A) : A.card ≤ (N + 1) / 2 := by
  sorry

theorem not_hasRepeatedUnitSolution_upperHalf (N : ℕ) : ¬ HasRepeatedUnitSolution (upperHalf N) := by
  sorry

end Erdos301Challenge
