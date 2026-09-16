import Erdos439Power.MeshNormalization

open scoped BigOperators
open Erdos439 Erdos439.PowerDecay Erdos438.Fourier

namespace Erdos439Power

/-- A common prefix estimate loses only the uniform mesh constant after normalization. -/
lemma norm_transform_le_of_prefix (k L N t : ℕ) (hk : 1 ≤ k) (hN : 0 < N)
    (η : ℝ) (hη : 0 ≤ η)
    (hprefix : ∀ m ≤ N,
      ‖∑ n ∈ Finset.range m, phase (normalizedPower k L N) (-(t : ℤ))
        (normalizedPower k L n : ℤ)‖ ≤ η * N) :
    ‖transform (normalizedPower k L N)
      (fun s => (normalizedPowerWeight k L N s : ℂ)) (-(t : ℤ))‖ ≤
      2 * (2 : ℝ) ^ k * η := by
  have hT : 0 < (normalizedPower k L N : ℝ) := by
    exact_mod_cast (show 0 < normalizedPower k L N by
      simpa only [normalizedPower_zero] using normalizedPower_strictMono k L hN)
  have hgap := mul_normalizedPowerGap_le k L N hk hN
  have hsum := norm_gapPhaseSum_le_two_gap_mul_prefix k L N t (η * N)
    (by positivity) hprefix
  rw [transform_normalizedPowerWeight_eq k L N t hN, norm_mul]
  have hnorm : ‖((normalizedPower k L N : ℝ)⁻¹ : ℂ)‖ =
      (normalizedPower k L N : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  rw [hnorm]
  calc
    (normalizedPower k L N : ℝ)⁻¹ * ‖gapPhaseSum k L N t‖ ≤
        (normalizedPower k L N : ℝ)⁻¹ *
          (2 * normalizedPowerGap k L N * (η * N)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2 * (2 : ℝ) ^ k * η := by
      apply (inv_mul_le_iff₀ hT).mpr
      nlinarith [mul_le_mul_of_nonneg_right hgap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη)]

/-- The rectangular terminal majorant controls every prefix using one ambient length. -/
lemma prefix_le_of_terminal_majorant (k L N t : ℕ) (hk : 2 ≤ k) (hL : 0 < L)
    (R : ℝ) (hR : 0 ≤ R)
    (hmajor : powerTerminalProductMajorant k L N t N 1 (k - 1) ≤
      (N : ℝ) ^ (k - 1) * R) :
    ∀ m ≤ N, ‖∑ n ∈ Finset.range m,
      phase (normalizedPower k L N) (-(t : ℤ)) (normalizedPower k L n : ℤ)‖ ≤
      finiteWeylEnvelope N R (k - 1) := by
  intro m hm
  have hterminal := (powerWeylAggregate_le_productMajorant k L N t N hk hL
    [] m (k - 1) hm (by simp)).trans hmajor
  have h := powerWeylAggregate_le_scaledEnvelope k L N t N [] m 0 (k - 1) R
    hm hR (by simpa using hterminal)
  simpa only [powerWeylAggregate, iteratedPowerDifference, pow_zero, one_mul] using h

end Erdos439Power
