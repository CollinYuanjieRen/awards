import Mathlib

namespace ReciprocalSquares

/-- A strict lower mass ratio and a weak upper ratio force the Bernoulli
parameter into the compact interval `[1 / A, 1 / c]`. -/
theorem bernoulli_ratio_bounds
    (c A r W : ℝ) (hc : 1 < c) (hr : 0 < r)
    (hlo : c * r < W) (hhi : W ≤ A * r) :
    0 < W ∧ 1 < A ∧
      0 < r / W ∧ r / W < 1 ∧
      1 / A ≤ r / W ∧ r / W ≤ 1 / c := by
  have hcr : r < c * r := by
    have hpos : 0 < (c - 1) * r := mul_pos (sub_pos.mpr hc) hr
    nlinarith
  have hrW : r < W := hcr.trans hlo
  have hW : 0 < W := hr.trans hrW
  have hAr : r < A * r := hrW.trans_le hhi
  have hA : 1 < A := by
    exact lt_of_mul_lt_mul_right (by simpa only [one_mul] using hAr) hr.le
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hA0 : 0 < A := lt_trans (by norm_num) hA
  have hp0 : 0 < r / W := div_pos hr hW
  have hp1 : r / W < 1 := (div_lt_one hW).mpr hrW
  have hlow : 1 / A ≤ r / W := by
    apply (div_le_div_iff₀ hA0 hW).mpr
    nlinarith [hhi]
  have hupp : r / W ≤ 1 / c := by
    apply (div_le_div_iff₀ hW hc0).mpr
    nlinarith
  exact ⟨hW, hA, hp0, hp1, hlow, hupp⟩

/-- The compact ratio interval gives a positive uniform lower bound for the
Bernoulli variance. -/
theorem bernoulli_variance_lower
    (c A r W : ℝ) (hc : 1 < c) (hr : 0 < r)
    (hlo : c * r < W) (hhi : W ≤ A * r) :
    0 < (c - 1) / (A * c) ∧
      (c - 1) / (A * c) ≤ (r / W) * (1 - r / W) := by
  obtain ⟨hW, hA, hp0, hp1, hlow, hupp⟩ :=
    bernoulli_ratio_bounds c A r W hc hr hlo hhi
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hA0 : 0 < A := lt_trans (by norm_num) hA
  have hkappa : 0 < (c - 1) / (A * c) := by positivity
  have hcomp : 1 - 1 / c ≤ 1 - r / W := by linarith
  have hcomp0 : 0 ≤ 1 - 1 / c := by
    have hone : 1 / c < 1 := (div_lt_one hc0).mpr hc
    linarith
  have hmul : (1 / A) * (1 - 1 / c) ≤ (r / W) * (1 - r / W) :=
    mul_le_mul hlow hcomp hcomp0 hp0.le
  have hid : (c - 1) / (A * c) = (1 / A) * (1 - 1 / c) := by
    field_simp [ne_of_gt hA0, ne_of_gt hc0]
  exact ⟨hkappa, hid ▸ hmul⟩

/-- Both Bernoulli outcomes have probability at most the maximum of the two
endpoint bounds, and this maximum lies strictly between zero and one. -/
theorem bernoulli_atom_bound
    (c A r W : ℝ) (hc : 1 < c) (hr : 0 < r)
    (hlo : c * r < W) (hhi : W ≤ A * r) :
    0 < max (1 - 1 / A) (1 / c) ∧
      max (1 - 1 / A) (1 / c) < 1 ∧
      max (r / W) (1 - r / W) ≤ max (1 - 1 / A) (1 / c) := by
  obtain ⟨hW, hA, hp0, hp1, hlow, hupp⟩ :=
    bernoulli_ratio_bounds c A r W hc hr hlo hhi
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hA0 : 0 < A := lt_trans (by norm_num) hA
  have hleft0 : 0 < 1 - 1 / A := by
    have hone : 1 / A < 1 := (div_lt_one hA0).mpr hA
    linarith
  have hright0 : 0 < 1 / c := one_div_pos.mpr hc0
  have hleft1 : 1 - 1 / A < 1 := by
    have : 0 < 1 / A := one_div_pos.mpr hA0
    linarith
  have hright1 : 1 / c < 1 := (div_lt_one hc0).mpr hc
  have hq0 : 0 < max (1 - 1 / A) (1 / c) :=
    hleft0.trans_le (le_max_left _ _)
  have hq1 : max (1 - 1 / A) (1 / c) < 1 :=
    max_lt hleft1 hright1
  have hcomp : 1 - r / W ≤ 1 - 1 / A := by linarith
  have hmax : max (r / W) (1 - r / W) ≤ max (1 - 1 / A) (1 / c) := by
    apply max_le
    · exact hupp.trans (le_max_right _ _)
    · exact hcomp.trans (le_max_left _ _)
  exact ⟨hq0, hq1, hmax⟩

end ReciprocalSquares
