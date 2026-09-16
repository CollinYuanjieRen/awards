import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory

namespace DiskDiscrepancy

/-- The nonnegative sinc-squared kernel at scale `a`. -/
noncomputable def sincKernel (a t : ℝ) : ℝ :=
  a * (Real.sinc (Real.pi * a * t)) ^ 2

/-- The sinc-squared kernel is pointwise nonnegative at positive scales. -/
theorem sincKernel_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ sincKernel a t := by
  exact mul_nonneg ha.le (sq_nonneg _)

/-- The sinc-squared kernel takes the value `a` at the origin. -/
@[simp]
theorem sincKernel_zero (a : ℝ) : sincKernel a 0 = a := by
  simp [sincKernel]

/-- The square of sinc is bounded by an integrable Cauchy kernel. -/
theorem sinc_sq_le_cauchy (u : ℝ) :
    Real.sinc u ^ 2 ≤ 2 * (1 + u ^ 2)⁻¹ := by
  have hsinc : Real.sinc u ^ 2 ≤ 1 := by
    simpa [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (Real.sinc u)) zero_le_one).2 (Real.abs_sinc_le_one u)
  have husinc : u ^ 2 * Real.sinc u ^ 2 ≤ 1 := by
    by_cases hu : u = 0
    · simp [hu]
    · rw [Real.sinc_of_ne_zero hu]
      field_simp
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (Real.sin u)) zero_le_one).2 (Real.abs_sin_le_one u)
  have hden : 0 < 1 + u ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hden]
  nlinarith

/-- The sinc-squared kernel is integrable at every positive scale. -/
theorem integrable_sincKernel {a : ℝ} (ha : 0 < a) : Integrable (sincKernel a) := by
  let c : ℝ := Real.pi * a
  let g : ℝ → ℝ := fun t ↦ 2 * a * (1 + (c * t) ^ 2)⁻¹
  have hc : c ≠ 0 := mul_ne_zero Real.pi_ne_zero ha.ne'
  have hg : Integrable g := by
    exact (integrable_inv_one_add_sq.comp_mul_left' hc).const_mul (2 * a)
  refine hg.mono ?_ ?_
  · exact (Real.continuous_sinc.comp
      ((continuous_const.mul continuous_const).mul continuous_id)).pow 2 |>.const_mul a
      |>.aestronglyMeasurable
  · filter_upwards [] with t
    have hbound := sinc_sq_le_cauchy (c * t)
    have hkernel : 0 ≤ sincKernel a t := sincKernel_nonneg ha t
    have hg_nonneg : 0 ≤ g t := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hkernel, abs_of_nonneg hg_nonneg]
    simpa [sincKernel, g, c, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hbound ha.le

/-- The integral of the sinc-squared kernel is at most `2` at every positive scale. -/
theorem integral_sincKernel_le_two {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, sincKernel a t) ≤ 2 := by
  let c : ℝ := Real.pi * a
  let g : ℝ → ℝ := fun t ↦ 2 * a * (1 + (c * t) ^ 2)⁻¹
  have hc : c ≠ 0 := mul_ne_zero Real.pi_ne_zero ha.ne'
  have hg : Integrable g := by
    exact (integrable_inv_one_add_sq.comp_mul_left' hc).const_mul (2 * a)
  calc
    (∫ t : ℝ, sincKernel a t) ≤ ∫ t : ℝ, g t := by
      refine integral_mono (integrable_sincKernel ha) hg fun t ↦ ?_
      simpa [sincKernel, g, c, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left (sinc_sq_le_cauchy (c * t)) ha.le
    _ = 2 := by
      rw [show (∫ t : ℝ, g t) = 2 * a * ∫ t : ℝ, (1 + (c * t) ^ 2)⁻¹ by
        exact integral_const_mul (2 * a) _]
      rw [MeasureTheory.Measure.integral_comp_mul_left
        (fun u : ℝ ↦ (1 + u ^ 2)⁻¹) c]
      simp only [integral_univ_inv_one_add_sq, smul_eq_mul]
      rw [abs_of_pos (inv_pos.mpr (mul_pos Real.pi_pos ha))]
      field_simp [c, Real.pi_ne_zero, ha.ne']

end DiskDiscrepancy
