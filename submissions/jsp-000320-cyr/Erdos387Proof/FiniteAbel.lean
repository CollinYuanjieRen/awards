import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Finite partial summation with the weight variation retained explicitly. -/

namespace Erdos387Proof.FiniteAbel

open scoped BigOperators

noncomputable def variationMass (w : ℕ → ℂ) (N : ℕ) : ℝ :=
  ‖w (N - 1)‖ + ∑ i ∈ Finset.range (N - 1), ‖w (i + 1) - w i‖

theorem norm_sum_mul_le_variation (w f : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hpartial : ∀ m ≤ N, ‖∑ i ∈ Finset.range m, f i‖ ≤ B) :
    ‖∑ i ∈ Finset.range N, w i * f i‖ ≤ variationMass w N * B := by
  have hid := Finset.sum_range_by_parts w f N
  simp only [smul_eq_mul] at hid
  rw [hid]
  calc
    _ ≤ ‖w (N - 1) * ∑ i ∈ Finset.range N, f i‖ +
        ‖∑ i ∈ Finset.range (N - 1),
          (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), f j‖ := norm_sub_le _ _
    _ ≤ ‖w (N - 1)‖ * B +
        ∑ i ∈ Finset.range (N - 1), ‖w (i + 1) - w i‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpartial N le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (hpartial (i + 1) (by have := Finset.mem_range.mp hi; omega)) (norm_nonneg _)
    _ = variationMass w N * B := by rw [variationMass, add_mul, Finset.sum_mul]

noncomputable def mixedVariationMass (w : ℕ → ℕ → ℂ) (N M : ℕ) : ℝ :=
  variationMass (w (N - 1)) M +
    ∑ i ∈ Finset.range (N - 1), variationMass (fun j => w (i + 1) j - w i j) M

/-- Weights need not separate as a product of a row weight and a column weight.
The mixed variation is paid for explicitly; the cancellation input consists of
actual rectangular partial sums of the unweighted array. -/
theorem norm_double_sum_mul_le_mixedVariation
    (w f : ℕ → ℕ → ℂ) (N M : ℕ) {B : ℝ}
    (hpartial : ∀ n ≤ N, ∀ m ≤ M,
      ‖∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f i j‖ ≤ B) :
    ‖∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, w i j * f i j‖ ≤
      mixedVariationMass w N M * B := by
  let P : ℕ → ℕ → ℂ := fun n j => ∑ i ∈ Finset.range n, f i j
  have hid : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, w i j * f i j) =
      (∑ j ∈ Finset.range M, w (N - 1) j * P N j) -
        ∑ i ∈ Finset.range (N - 1), ∑ j ∈ Finset.range M,
          (w (i + 1) j - w i j) * P (i + 1) j := by
    rw [Finset.sum_comm]
    have heach (j : ℕ) := Finset.sum_range_by_parts (fun i => w i j) (fun i => f i j) N
    simp only [smul_eq_mul] at heach
    simp_rw [heach]
    rw [Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  have hP (n : ℕ) (hn : n ≤ N) :
      ∀ m ≤ M, ‖∑ j ∈ Finset.range m, P n j‖ ≤ B := by
    intro m hm
    dsimp [P]
    rw [Finset.sum_comm]
    exact hpartial n hn m hm
  rw [hid]
  calc
    _ ≤ ‖∑ j ∈ Finset.range M, w (N - 1) j * P N j‖ +
        ‖∑ i ∈ Finset.range (N - 1), ∑ j ∈ Finset.range M,
          (w (i + 1) j - w i j) * P (i + 1) j‖ := norm_sub_le _ _
    _ ≤ variationMass (w (N - 1)) M * B +
        ∑ i ∈ Finset.range (N - 1),
          variationMass (fun j => w (i + 1) j - w i j) M * B := by
      apply add_le_add
      · exact norm_sum_mul_le_variation _ _ M (hP N le_rfl)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_mul_le_variation _ _ M
          (hP (i + 1) (by have := Finset.mem_range.mp hi; omega))
    _ = mixedVariationMass w N M * B := by
      rw [mixedVariationMass, add_mul, Finset.sum_mul]

end Erdos387Proof.FiniteAbel
