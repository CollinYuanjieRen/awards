import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Erdos441

theorem lcm_gt_of_separated_lower_bounds (X a b d : ℝ) (u v gamma : ℕ)
    (hX : 0 < X) (ha : 0 < a) (hb : 0 < b) (hgamma : 0 < gamma)
    (hu : a * Real.sqrt X < (u : ℝ)) (hv : b * Real.sqrt X < (v : ℝ))
    (hg : (gamma : ℝ) * (Nat.gcd u v : ℝ) ≤ d)
    (hd : d ≤ (gamma : ℝ) * a * b) : X < (Nat.lcm u v : ℝ) := by
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hgp : (0 : ℝ) < gamma := Nat.cast_pos.mpr hgamma
  have hu0 : (0 : ℝ) < u := (mul_pos ha hs).trans hu
  have hp : a * b * X < (u : ℝ) * v := by
    calc
      _ = (a * Real.sqrt X) * (b * Real.sqrt X) := by
        rw [mul_mul_mul_comm, Real.mul_self_sqrt hX.le]
      _ < (u : ℝ) * v := mul_lt_mul hu hv.le (mul_pos hb hs) hu0.le
  have hid : (Nat.gcd u v : ℝ) * (Nat.lcm u v : ℝ) = (u : ℝ) * v := by
    exact_mod_cast Nat.gcd_mul_lcm u v
  by_contra hnot
  have hl : (Nat.lcm u v : ℝ) ≤ X := le_of_not_gt hnot
  have hupper : (gamma : ℝ) * ((u : ℝ) * v) ≤ (gamma : ℝ) * (a * b * X) := by
    calc
      _ = ((gamma : ℝ) * (Nat.gcd u v : ℝ)) * (Nat.lcm u v : ℝ) := by rw [mul_assoc, hid]
      _ ≤ ((gamma : ℝ) * (Nat.gcd u v : ℝ)) * X :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ d * X := mul_le_mul_of_nonneg_right hg hX.le
      _ ≤ ((gamma : ℝ) * a * b) * X := mul_le_mul_of_nonneg_right hd hX.le
      _ = _ := by ring
  exact (not_lt_of_ge hupper) (mul_lt_mul_of_pos_left hp hgp)

end Erdos441

#print axioms Erdos441.lcm_gt_of_separated_lower_bounds
