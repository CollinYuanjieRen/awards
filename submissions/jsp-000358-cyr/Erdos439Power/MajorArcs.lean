import Erdos439Power.MajorArcCore
import Erdos439Power.MajorScalar

open scoped BigOperators
open Erdos439 Erdos439.PowerDecay Erdos438.Fourier

namespace Erdos439Power

/-- A finite major-arc bound, including exact cancellation at denominator one. -/
theorem norm_transform_le_major_arc (k L N t q a Q : ℕ) [NeZero q]
    (hN : 0 < N) (hq : 0 < q) (hQ : 0 < Q)
    (ht : t < normalizedPower k L N) (ht0 : t ≠ 0)
    (η : ℝ) (hη : 0 ≤ η)
    (hmean : 1 < q →
      ‖𝔼 x : ZMod q, polynomialPhase q a (normalizedPowerPolynomial k L) x‖ ≤ η)
    (happrox : (q : ℝ) * |(t : ℝ) / normalizedPower k L N - (a : ℝ) / q| ≤ 1 / (Q : ℝ)) :
    ‖transform (normalizedPower k L N)
      (fun s => (normalizedPowerWeight k L N s : ℂ)) (-(t : ℤ))‖ ≤
      η + 4 * q * normalizedPowerGap k L N / normalizedPower k L N +
        4 * Real.pi * normalizedPowerGap k L N / Q := by
  have hT : 0 < (normalizedPower k L N : ℝ) := by
    exact_mod_cast (show 0 < normalizedPower k L N by
      simpa only [normalizedPower_zero] using normalizedPower_strictMono k L hN)
  let u : ℝ := |(t : ℝ) / normalizedPower k L N - (a : ℝ) / q|
  have hu : 0 ≤ u := abs_nonneg _
  have hg : 0 ≤ normalizedPowerGap k L N := (normalizedPowerGap_pos _ _ _).le
  have hraw : ‖gapPhaseSum k L N t‖ ≤ η * normalizedPower k L N +
      2 * q * (2 * normalizedPowerGap k L N +
        (2 * Real.pi * u) * normalizedPowerGap k L N * normalizedPower k L N) := by
    by_cases hq1 : q = 1
    · subst q
      have h := norm_gapPhaseSum_le_at_integer k L N t a hN ht ht0
      dsimp only at h
      rw [abs_major_phase] at h
      dsimp [u]
      simp only [Nat.cast_one, div_one]
      have hn : 0 ≤ (2 * Real.pi * |(t : ℝ) / normalizedPower k L N - a|) *
          normalizedPowerGap k L N * normalizedPower k L N := by positivity
      nlinarith [mul_nonneg hη hT.le]
    · have h := norm_gapPhaseSum_le_main_add_error k L N t q a hN hq
      dsimp only at h
      rw [abs_major_phase] at h
      have hm := mul_le_mul_of_nonneg_right (hmean (by omega)) hT.le
      dsimp [u]
      linarith
  rw [norm_transform_eq_inv_norm_gap k L N t hN]
  exact normalized_major_error_bound _ _ _ _ _ _ _ hT hg (by positivity)
    (by exact_mod_cast hQ) happrox hraw

/-- Substituting the common fourth-power length gives an explicit vanishing error. -/
theorem norm_transform_le_major_parameter (k L C M t q a : ℕ) [NeZero q]
    (hk : 1 ≤ k) (hM : 2 ≤ M) (hq : 0 < q) (hqM : q ≤ C * M)
    (ht : t < normalizedPower k L (M ^ 4)) (ht0 : t ≠ 0)
    (η : ℝ) (hη : 0 ≤ η)
    (hmean : 1 < q →
      ‖𝔼 x : ZMod q, polynomialPhase q a (normalizedPowerPolynomial k L) x‖ ≤ η)
    (happrox : (q : ℝ) * |(t : ℝ) / normalizedPower k L (M ^ 4) - (a : ℝ) / q| ≤
      1 / ((M ^ (4 * k - 1) : ℕ) : ℝ)) :
    ‖transform (normalizedPower k L (M ^ 4))
      (fun s => (normalizedPowerWeight k L (M ^ 4) s : ℂ)) (-(t : ℤ))‖ ≤
      η + (4 * (2 : ℝ) ^ k * ((C : ℝ) + Real.pi * normalizedPower k L 1)) / (M : ℝ) ^ 3 := by
  have h := norm_transform_le_major_arc k L (M ^ 4) t q a (M ^ (4 * k - 1))
    (by positivity) hq (by positivity) ht ht0 η hη hmean happrox
  have hp := major_parameter_bound k L C M q hk hM hqM
  dsimp only at hp
  linarith

end Erdos439Power
