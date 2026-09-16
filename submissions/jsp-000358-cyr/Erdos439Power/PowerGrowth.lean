import Erdos439Power.MeshNormalization

open scoped BigOperators
open Erdos439

namespace Erdos439Power

/-- Positive coefficients give a uniform polynomial growth bound with the
literal coefficient sum as constant. -/
lemma normalizedPower_le_value_one_mul_pow (k L N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    normalizedPower k L N ≤ normalizedPower k L 1 * N ^ k := by
  unfold normalizedPower
  simp only [one_pow, mul_one]
  rw [add_mul, one_mul, Finset.sum_mul]
  apply Nat.add_le_add
  · calc
      N = N ^ 1 := by simp
      _ ≤ N ^ k := Nat.pow_le_pow_right hN hk
  · apply Finset.sum_le_sum
    intro j hj
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (Finset.mem_Icc.mp hj).2)

lemma normalizedPower_index_le (k L N : ℕ) : N ≤ normalizedPower k L N := by
  unfold normalizedPower
  omega

lemma normalizedPowerGap_le_growth (k L N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    normalizedPowerGap k L N ≤
      (2 : ℝ) ^ k * normalizedPower k L 1 * (N : ℝ) ^ (k - 1) := by
  have hmesh := mul_normalizedPowerGap_le k L N hk hN
  have hgrowth : (normalizedPower k L N : ℝ) ≤
      normalizedPower k L 1 * (N : ℝ) ^ k := by
    exact_mod_cast normalizedPower_le_value_one_mul_pow k L N hk hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (mul_le_mul_iff_right₀ hNpos).mp
  have hexp : k = (k - 1) + 1 := by omega
  calc
    (N : ℝ) * normalizedPowerGap k L N ≤ (2 : ℝ) ^ k * normalizedPower k L N := hmesh
    _ ≤ (2 : ℝ) ^ k * (normalizedPower k L 1 * (N : ℝ) ^ k) := by gcongr
    _ = N * ((2 : ℝ) ^ k * normalizedPower k L 1 * (N : ℝ) ^ (k - 1)) := by
      conv_lhs => arg 2; arg 2; rw [hexp, pow_succ]
      ring

end Erdos439Power
