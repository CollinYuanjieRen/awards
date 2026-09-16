import JSP620.External.Erdos754

/-!
# Two orthogonal circles in `ℝ⁴` (the Lenz construction)

Supporting geometry for the lower bound in Erdős Problem 754 / JSP-000620.

Points of the two circles are encoded by complex numbers `w` with `normSq w = 1 / 2`:
`e1 w = (w.re, w.im, 0, 0)` lies on the circle in the first coordinate plane and
`e2 w = (0, 0, w.re, w.im)` on the circle in the second coordinate plane.  Any point of
the first circle is at distance one from every point of the second circle, and the
rotation by a right angle (`w ↦ w * I`) moves a point of a circle to a point at
distance one on the same circle.
-/

open Complex Finset

namespace Erdos754Lower

open Erdos754

/-- The common radius `1 / √2` of the two circles. -/
noncomputable def ρ : ℝ := (Real.sqrt 2)⁻¹

lemma ρ_pos : 0 < ρ := by
  unfold ρ
  positivity

lemma ρ_ne_zero : ρ ≠ 0 := ρ_pos.ne'

lemma ρ_mul_self : ρ * ρ = 1 / 2 := by
  unfold ρ
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- A point of the first circle, placed in the first coordinate plane of `ℝ⁴`. -/
noncomputable def e1 (w : ℂ) : E4 := !₂[w.re, w.im, 0, 0]

/-- A point of the second circle, placed in the second coordinate plane of `ℝ⁴`. -/
noncomputable def e2 (w : ℂ) : E4 := !₂[0, 0, w.re, w.im]

@[simp] lemma e1_zero (w : ℂ) : e1 w 0 = w.re := rfl
@[simp] lemma e1_one (w : ℂ) : e1 w 1 = w.im := rfl
@[simp] lemma e1_two (w : ℂ) : e1 w 2 = 0 := rfl
@[simp] lemma e1_three (w : ℂ) : e1 w 3 = 0 := rfl
@[simp] lemma e2_zero (w : ℂ) : e2 w 0 = 0 := rfl
@[simp] lemma e2_one (w : ℂ) : e2 w 1 = 0 := rfl
@[simp] lemma e2_two (w : ℂ) : e2 w 2 = w.re := rfl
@[simp] lemma e2_three (w : ℂ) : e2 w 3 = w.im := rfl

lemma e1_injective : Function.Injective e1 := by
  intro w v h
  have h0 := congrArg (fun x : E4 => x 0) h
  have h1 := congrArg (fun x : E4 => x 1) h
  simp only [e1_zero, e1_one] at h0 h1
  exact Complex.ext h0 h1

lemma e2_injective : Function.Injective e2 := by
  intro w v h
  have h0 := congrArg (fun x : E4 => x 2) h
  have h1 := congrArg (fun x : E4 => x 3) h
  simp only [e2_two, e2_three] at h0 h1
  exact Complex.ext h0 h1

lemma e1_ne_e2 {w v : ℂ} (hw : w ≠ 0) : e1 w ≠ e2 v := by
  intro h
  have h0 := congrArg (fun x : E4 => x 0) h
  have h1 := congrArg (fun x : E4 => x 1) h
  simp only [e1_zero, e1_one, e2_zero, e2_one] at h0 h1
  exact hw (Complex.ext h0 h1)

lemma dist_sq_e1_e1 (w v : ℂ) : dist (e1 w) (e1 v) ^ 2 = normSq (w - v) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_four]
  simp only [e1_zero, e1_one, e1_two, e1_three, Real.dist_eq, sq_abs, normSq_apply,
    Complex.sub_re, Complex.sub_im]
  ring

lemma dist_sq_e2_e2 (w v : ℂ) : dist (e2 w) (e2 v) ^ 2 = normSq (w - v) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_four]
  simp only [e2_zero, e2_one, e2_two, e2_three, Real.dist_eq, sq_abs, normSq_apply,
    Complex.sub_re, Complex.sub_im]
  ring

lemma dist_sq_e1_e2 (w v : ℂ) : dist (e1 w) (e2 v) ^ 2 = normSq w + normSq v := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_four]
  simp only [e1_zero, e1_one, e1_two, e1_three, e2_zero, e2_one, e2_two, e2_three,
    Real.dist_eq, sq_abs, normSq_apply]
  ring

lemma dist_eq_one_of_sq {x y : E4} (h : dist x y ^ 2 = 1) : dist x y = 1 := by
  have := (pow_left_inj₀ dist_nonneg zero_le_one two_ne_zero).mp (by rw [h]; norm_num)
  exact this

lemma dist_e1_e2 {w v : ℂ} (hw : normSq w = 1 / 2) (hv : normSq v = 1 / 2) :
    dist (e1 w) (e2 v) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e1_e2, hw, hv]
  norm_num

lemma dist_e2_e1 {w v : ℂ} (hw : normSq w = 1 / 2) (hv : normSq v = 1 / 2) :
    dist (e2 w) (e1 v) = 1 := by
  rw [dist_comm]
  exact dist_e1_e2 hv hw

lemma normSq_sub_mul_I (w : ℂ) : normSq (w - w * I) = 2 * normSq w := by
  have : w - w * I = w * (1 - I) := by ring
  rw [this, normSq_mul]
  simp [normSq_apply]
  ring

lemma normSq_sub_mul_neg_I (w : ℂ) : normSq (w - w * (-I)) = 2 * normSq w := by
  have : w - w * (-I) = w * (1 + I) := by ring
  rw [this, normSq_mul]
  simp [normSq_apply]
  ring

lemma dist_e1_rot {w : ℂ} (hw : normSq w = 1 / 2) : dist (e1 w) (e1 (w * I)) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e1_e1, normSq_sub_mul_I, hw]
  norm_num

lemma dist_e1_rot' {w : ℂ} (hw : normSq w = 1 / 2) : dist (e1 w) (e1 (w * (-I))) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e1_e1, normSq_sub_mul_neg_I, hw]
  norm_num

lemma dist_e2_rot {w : ℂ} (hw : normSq w = 1 / 2) : dist (e2 w) (e2 (w * I)) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e2_e2, normSq_sub_mul_I, hw]
  norm_num

lemma dist_e2_rot' {w : ℂ} (hw : normSq w = 1 / 2) : dist (e2 w) (e2 (w * (-I))) = 1 := by
  apply dist_eq_one_of_sq
  rw [dist_sq_e2_e2, normSq_sub_mul_neg_I, hw]
  norm_num

lemma ne_zero_of_normSq {w : ℂ} (hw : normSq w = 1 / 2) : w ≠ 0 := by
  intro h
  rw [h, normSq_zero] at hw
  norm_num at hw

lemma mul_I_ne_self {w : ℂ} (hw : w ≠ 0) : w * I ≠ w := by
  intro h
  have : w * (I - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hw h0
  · have := congrArg Complex.re h0
    simp at this

lemma mul_neg_I_ne_self {w : ℂ} (hw : w ≠ 0) : w * (-I) ≠ w := by
  intro h
  have : w * (-I - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hw h0
  · have := congrArg Complex.re h0
    simp at this

lemma mul_I_ne_mul_neg_I {w : ℂ} (hw : w ≠ 0) : w * I ≠ w * (-I) := by
  intro h
  have : w * (2 * I) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hw h0
  · have := congrArg Complex.im h0
    simp at this

end Erdos754Lower
