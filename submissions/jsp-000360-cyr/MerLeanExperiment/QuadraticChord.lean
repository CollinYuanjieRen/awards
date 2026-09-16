import Mathlib.Tactic

namespace Erdos441

theorem quadratic_nonneg_between (a b u A B C : ℝ) (ha : a ≤ u) (hb : u ≤ b)
    (hA : A ≤ 0) (hleft : 0 ≤ A * a ^ 2 + B * a + C)
    (hright : 0 ≤ A * b ^ 2 + B * b + C) :
    0 ≤ A * u ^ 2 + B * u + C := by
  by_cases heq : a = b
  · have hu : u = a := by linarith
    simpa only [hu] using hleft
  have hgap : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (ha.trans hb) heq)
  have hid : (b - a) * (A * u ^ 2 + B * u + C) =
      (b - u) * (A * a ^ 2 + B * a + C) +
      (u - a) * (A * b ^ 2 + B * b + C) +
      (-A) * (u - a) * (b - u) * (b - a) := by ring
  have hmul : 0 ≤ (b - a) * (A * u ^ 2 + B * u + C) := by
    rw [hid]
    have hua := sub_nonneg.mpr ha
    have hbu := sub_nonneg.mpr hb
    have hnA := neg_nonneg.mpr hA
    positivity
  by_contra hn
  exact (not_lt_of_ge hmul) (mul_neg_of_pos_of_neg hgap (lt_of_not_ge hn))

end Erdos441

#print axioms Erdos441.quadratic_nonneg_between
