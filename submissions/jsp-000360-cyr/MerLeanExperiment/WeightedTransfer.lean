import MerLeanExperiment.PrefixDot
import MerLeanExperiment.SuffixMax

namespace Erdos441

open scoped BigOperators

theorem weighted_prefix_transfer_of_forward_moves {n r : ℕ} (α β : Fin n → ℝ)
    (k : Fin r → Fin n → ℕ) (δ : Fin r → ℝ) (B : ℝ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (hδ : ∀ j, 0 ≤ δ j)
    (hprefix : ∀ t : Fin n,
      ∑ i ∈ Finset.Iic t, β i ≤ ∑ i ∈ Finset.Iic t, ∑ j, δ j * k j i)
    (hmoves : ∀ j (φ : Fin n → Fin n), (∀ i, i ≤ φ i) →
      ∑ i, (k j i : ℝ) * α (φ i) ≤ B) :
    ∑ i, β i * α i ≤ B * ∑ j, δ j := by
  classical
  obtain ⟨hmajor, hanti, hattain⟩ := suffix_max_spec α
  choose φ hφ hφval using hattain
  let M : Fin n → ℝ := suffixMax α
  let c : Fin n → ℝ := fun i ↦ ∑ j, δ j * (k j i : ℝ)
  have hMnonneg : ∀ i, 0 ≤ M i := fun i ↦ (hα i).trans (hmajor i)
  have hβα : (∑ i, β i * α i) ≤ ∑ i, β i * M i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hmajor i) (hβ i)
  have hβc : (∑ i, β i * M i) ≤ ∑ i, c i * M i := by
    apply dot_le_of_prefix_le β c M hMnonneg hanti
    intro t
    simpa [c] using hprefix t
  have hmoveM : ∀ j, (∑ i, (k j i : ℝ) * M i) ≤ B := by
    intro j
    have hj := hmoves j φ hφ
    simpa [M, hφval] using hj
  have hexchange :
      (∑ i, c i * M i) = ∑ j, δ j * ∑ i, (k j i : ℝ) * M i := by
    simp only [c, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr with j
    rw [Finset.mul_sum]
    congr with i
    ring
  calc
    (∑ i, β i * α i) ≤ ∑ i, β i * M i := hβα
    _ ≤ ∑ i, c i * M i := hβc
    _ = ∑ j, δ j * ∑ i, (k j i : ℝ) * M i := hexchange
    _ ≤ ∑ j, δ j * B := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hmoveM j) (hδ j)
    _ = B * ∑ j, δ j := by rw [Finset.mul_sum]; simp [mul_comm]

end Erdos441
