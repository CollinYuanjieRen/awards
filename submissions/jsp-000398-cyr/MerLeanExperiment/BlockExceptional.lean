import MerLeanExperiment.BlockConstruction

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos492Real

noncomputable section

/-- Pull back the finite exceptional set under the actual block rescaling. -/
def scaledExceptional (E : ℕ → Set ℝ) (k : ℕ) : Set ℝ :=
  {α | α / (blockCutoff (k + 1) : ℝ) ∈ E k}

theorem volume_scaledExceptional (E : ℕ → Set ℝ) (k : ℕ) :
    volume (scaledExceptional E k) =
      ENNReal.ofReal (blockCutoff (k + 1) : ℝ) * volume (E k) := by
  have hB : (0 : ℝ) < blockCutoff (k + 1) := by
    exact_mod_cast blockCutoff_pos (k + 1)
  change volume ((fun α : ℝ => α / (blockCutoff (k + 1) : ℝ)) ⁻¹' E k) = _
  simp only [div_eq_mul_inv]
  rw [Real.volume_preimage_mul_right (inv_ne_zero (ne_of_gt hB))]
  simp only [inv_inv, abs_of_pos hB]

theorem volume_scaledExceptional_le_geometric (E : ℕ → Set ℝ)
    (hE : ∀ k, volume (E k) < ENNReal.ofReal (blockEpsilon k)) (k : ℕ) :
    volume (scaledExceptional E k) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
  rw [volume_scaledExceptional]
  calc
    _ ≤ ENNReal.ofReal (blockCutoff (k + 1) : ℝ) *
        ENNReal.ofReal (blockEpsilon k) := by
          gcongr
          exact (hE k).le
    _ = ENNReal.ofReal (1 / (2 : ℝ) ^ (k + 4)) := by
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      unfold blockEpsilon
      have hB : (blockCutoff (k + 1) : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (blockCutoff_pos (k + 1)))
      field_simp
    _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ k) := by
      apply ENNReal.ofReal_le_ofReal
      rw [pow_add]
      have hp : (0 : ℝ) < 2 ^ k := by positivity
      norm_num
    _ = (2⁻¹ : ℝ≥0∞) ^ k := by
      simp [one_div, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_pow, ENNReal.inv_pow]

/-- Borel--Cantelli applies to all positive parameters through a single
exceptional null set. No independence hypothesis is required. -/
theorem ae_eventually_avoids_scaledExceptional (E : ℕ → Set ℝ)
    (hE : ∀ k, volume (E k) < ENNReal.ofReal (blockEpsilon k)) :
    ∀ᵐ α : ℝ, ∀ᶠ k in atTop, α ∉ scaledExceptional E k := by
  apply MeasureTheory.ae_eventually_notMem
  apply ne_of_lt
  calc
    (∑' k, volume (scaledExceptional E k)) ≤ ∑' k, (2⁻¹ : ℝ≥0∞) ^ k :=
      ENNReal.tsum_le_tsum (volume_scaledExceptional_le_geometric E hE)
    _ = 2 := ENNReal.tsum_geometric_two
    _ < ∞ := by norm_num

end

end Erdos492Real
