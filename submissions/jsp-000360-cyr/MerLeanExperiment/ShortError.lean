import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace Erdos441

theorem eventually_short_interval_error (K : ℕ) (B : ℝ) (_hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in Filter.atTop,
    (K : ℝ) * B * x ^ (1 / 4 : ℝ) + K ≤ ε * Real.sqrt x := by
  have ht := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have he : ∀ᶠ x : ℝ in Filter.atTop,
      (K : ℝ) * (B + 1) / ε ≤ x ^ (1 / 4 : ℝ) :=
    ht.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), he] with x hx he
  have hx0 : 0 ≤ x := by linarith
  have hQ : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hcoef : (K : ℝ) * (B + 1) ≤ ε * x ^ (1 / 4 : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hε).mp he
  have hsq : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, Real.sqrt_eq_rpow]
    norm_num
  calc
    _ ≤ ((K : ℝ) * (B + 1)) * x ^ (1 / 4 : ℝ) := by
      have hkQ := mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
      nlinarith
    _ ≤ (ε * x ^ (1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = ε * Real.sqrt x := by rw [mul_assoc, ← sq, hsq]

end Erdos441

#print axioms Erdos441.eventually_short_interval_error
