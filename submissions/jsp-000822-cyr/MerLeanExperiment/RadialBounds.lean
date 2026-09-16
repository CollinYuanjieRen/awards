import MerLeanExperiment.RadialProfile
import MerLeanExperiment.CoordinateBox

open MeasureTheory

namespace DiskDiscrepancy

theorem abs_angularPrimitive_le_sq_div_two {z : ℝ} (hz : 0 ≤ z) :
    |angularPrimitive z| ≤ z ^ 2 / 2 := by
  calc
    _ ≤ ∫ t in 0..z, |t * angularKernel t| := by
      simpa only [angularPrimitive, Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (f := fun t ↦ t * angularKernel t) hz)
    _ ≤ ∫ t in 0..z, t := by
      apply intervalIntegral.integral_mono_on hz
        ((continuous_id.mul continuous_angularKernel).abs.intervalIntegrable _ _)
        (continuous_id.intervalIntegrable _ _)
      intro t ht
      change |t * angularKernel t| ≤ t
      rw [abs_mul, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_right ht.1 (abs_angularKernel_le_one t)
    _ = _ := by rw [integral_id]; ring

theorem abs_radialProfile_le_area {rho r : ℝ} (hrho : 0 ≤ rho) (hr : 0 ≤ r) :
    |radialProfile rho r| ≤ Real.pi * r ^ 2 := by
  by_cases hzero : rho = 0
  · simp [radialProfile, hzero, abs_of_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r))]
  have hrho_pos : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hzero)
  have hden : 0 < 2 * Real.pi * rho ^ 2 := by positivity
  rw [radialProfile, ite_eq_right hzero, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have h := abs_angularPrimitive_le_sq_div_two (z := 2 * Real.pi * rho * r) (by positivity)
  have heq : (2 * Real.pi * rho * r) ^ 2 / 2 = Real.pi * r ^ 2 * (2 * Real.pi * rho ^ 2) := by ring
  rw [heq] at h
  exact h

theorem measurable_radialProfile : Measurable (fun p : ℝ × ℝ ↦ radialProfile p.1 p.2) := by
  unfold radialProfile
  apply Measurable.ite
    (measurableSet_eq_fun measurable_fst measurable_const)
  · fun_prop
  · exact (continuous_angularPrimitive.measurable.comp
      (measurable_const.mul measurable_fst |>.mul measurable_snd)).div
      (measurable_const.mul (measurable_fst.pow_const 2))

theorem radialProfile_average_lower_on_box {R : ℝ} (hR : 1 ≤ R)
    {ξ : Plane} (hξ : ξ ∈ coordinateBox 4) :
    radialProfileConstant / 343 * R ≤
      (1 / R) * ∫ r in 0..R, radialProfile ‖ξ‖ r ^ 2 := by
  have hRpos : 0 < R := by linarith
  have hcpos := radialProfileConstant_pos
  have hnorm := norm_le_six_of_mem_frequencyBox hξ
  have hbase : 0 < 1 + R * ‖ξ‖ := by positivity
  have hden : (1 + R * ‖ξ‖) ^ 3 ≤ 343 * R ^ 3 := by
    have hb : 1 + R * ‖ξ‖ ≤ 7 * R := by nlinarith
    have h := pow_le_pow_left₀ hbase.le hb 3
    nlinarith [h]
  calc
    _ = radialProfileConstant * R ^ 4 / (343 * R ^ 3) := by
      field_simp [hRpos.ne']
    _ ≤ radialProfileConstant * R ^ 4 / (1 + R * ‖ξ‖) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity : 0 ≤ radialProfileConstant * R ^ 4)
        (by positivity) hden
    _ ≤ _ := radialProfile_average_lower hRpos (norm_nonneg ξ)

end DiskDiscrepancy
