import Mathlib

/-!
# Erdős problem #301 — definitions and the upper-half interval

This module fixes the vocabulary used for the scoped component of Erdős problem #301
(“Let `f(N)` be the size of the largest `A ⊆ {1, …, N}` such that there are no solutions to
`1/a = 1/b₁ + ⋯ + 1/b_k` with distinct `a, b₁, …, b_k ∈ A`”).

* `Erdos301.HasUnitSolution A` is the relation of the problem statement: some `a ∈ A` is the sum
  of the reciprocals of a nonempty set `B ⊆ A` of elements all different from `a` (so
  `a, b₁, …, b_k` are pairwise distinct elements of `A`, with `B = {b₁, …, b_k}` and `k ≥ 1`).
* `Erdos301.HasRepeatedUnitSolution A` is the variant in which the denominators `b_i` may repeat:
  `1/a = k · (1/b)` for a single `b ≠ a` in `A` and some `k ≥ 1`.  This is the reading of the
  Cambie–van Doorn remark that matches “there are distinct `a, b ∈ A` with `a ∣ b`”.
* `Erdos301.upperHalf N` is the extremal example `(N/2, N] ∩ ℕ`.
* `Erdos301.f N` is the problem's `f(N)`: the largest cardinality of a subset of `{1, …, N}`
  carrying no such relation.

The counting fact `card_upperHalf` records that `(N/2, N]` has exactly `⌈N/2⌉ = (N + 1) / 2`
elements.
-/

namespace Erdos301

/-- `HasUnitSolution A` holds when some `a ∈ A` satisfies `1/a = 1/b₁ + ⋯ + 1/b_k` for
pairwise distinct `b₁, …, b_k ∈ A` all different from `a` (`B = {b₁, …, b_k}`, `k ≥ 1`).
Arithmetic is carried out in `ℚ`. -/
def HasUnitSolution (A : Finset ℕ) : Prop := ∃ a ∈ A, ∃ B ⊆ A, a ∉ B ∧ B.Nonempty ∧ ((a : ℚ))⁻¹ = ∑ b ∈ B, ((b : ℚ))⁻¹

/-- `HasRepeatedUnitSolution A` holds when some `a ∈ A` satisfies `1/a = k · (1/b)` for another
element `b ∈ A`, `b ≠ a`, and some `k ≥ 1`; i.e. the relation `1/a = 1/b₁ + ⋯ + 1/b_k` in which
all the denominators `b_i` are equal to a single `b ≠ a`. -/
def HasRepeatedUnitSolution (A : Finset ℕ) : Prop := ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ k : ℕ, 0 < k ∧ ((a : ℚ))⁻¹ = k * ((b : ℚ))⁻¹

/-- The upper half `(N/2, N] ∩ ℕ` of `{1, …, N}`, i.e. the integers `1 ≤ n ≤ N` with `N < 2n`. -/
def upperHalf (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun n => N < 2 * n)

open Classical in
/-- `f N` is the size of the largest `A ⊆ {1, …, N}` with no solution to
`1/a = 1/b₁ + ⋯ + 1/b_k` in distinct elements of `A`.  The predicate `¬ HasUnitSolution A` is
not decidable, so the filter uses classical decidability and `f` is noncomputable. -/
noncomputable def f (N : ℕ) : ℕ := ((Finset.Icc 1 N).powerset.filter (fun A => ¬ HasUnitSolution A)).sup Finset.card

/-- Membership in `upperHalf N`: the positivity constraint `1 ≤ n` is implied by `N < 2n`
whenever `n ≤ N`, so membership is exactly `n ≤ N ∧ N < 2n`. -/
theorem mem_upperHalf {N n : ℕ} : n ∈ upperHalf N ↔ n ≤ N ∧ N < 2 * n := by
  simp only [upperHalf, Finset.mem_filter, Finset.mem_Icc]
  omega

/-- `upperHalf N` is the interval `(⌊N/2⌋, N]`. -/
theorem upperHalf_eq_Ioc (N : ℕ) : upperHalf N = Finset.Ioc (N / 2) N := by
  ext n
  simp only [upperHalf, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- **T3.** The upper half `(N/2, N]` has exactly `⌈N/2⌉ = (N + 1) / 2` elements. -/
theorem card_upperHalf (N : ℕ) : (upperHalf N).card = (N + 1) / 2 := by
  rw [upperHalf_eq_Ioc, Nat.card_Ioc]
  omega

end Erdos301
