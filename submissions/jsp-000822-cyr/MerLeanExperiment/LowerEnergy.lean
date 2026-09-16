import MerLeanExperiment.AveragedEnergy
import MerLeanExperiment.DiskTransformBridge

open MeasureTheory
open scoped FourierTransform

namespace DiskDiscrepancy

theorem profileEnergy_eq_fourier_norm_sq (P : Finset Plane) (M : ℝ)
    {r : ℝ} (hr : 0 ≤ r) (ξ : Plane) :
    profileEnergy P M r ξ = ‖(𝓕 (cutoffSignal P M r) : Plane → ℂ) ξ‖ ^ 2 := by
  rw [fourier_cutoffSignal, fourier_diskIndicator_eq_profile hr]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rfl

theorem profileEnergy_integral_le_spatial (P : Finset Plane) (M : ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    (∫ ξ in coordinateBox 4, profileEnergy P M r ξ) ≤
      ∫ x : Plane, ‖cutoffSignal P M r x‖ ^ 2 := by
  simp_rw [profileEnergy_eq_fourier_norm_sq P M hr]
  rw [← cutoffSignal_plancherel P M hr]
  apply setIntegral_le_integral
  · exact (memLp_fourier_of_integrable_memLp_two (integrable_cutoffSignal P M r)
      (memLp_cutoffSignal P M hr)).integrable_norm_pow (by norm_num : 2 ≠ 0)
  · exact Filter.Eventually.of_forall fun ξ ↦ sq_nonneg _

/-- Comparison of the genuine averaged Fourier lower bound with the actual spatial cutoff. -/
theorem cutoff_energy_comparison {S : Set Plane} (hS : Admissible S)
    {M R D : ℝ} (hR : 1 ≤ R) (hM : R < M) (hD : D ≤ R ^ 2)
    (hbound : ∀ x : Plane, ∀ r : ℝ, 0 < r → r ≤ R → discrepancy S x r ≤ D) :
    (8 * radialProfileConstant / 343) * R * (cutoffPoints S hS M).card ≤
      4 * M ^ 2 * D ^ 2 + 16 * (2 * Real.pi + 1) ^ 2 * M * R ^ 5 := by
  have hRpos : 0 < R := by linarith
  let P := cutoffPoints S hS M
  let H := 4 * M ^ 2 * D ^ 2 + 16 * (2 * Real.pi + 1) ^ 2 * M * R ^ 5
  have hjoint := integrable_profileEnergy P M hRpos
  have hfin : volume (Set.Ioc (0 : ℝ) R) ≠ ⊤ :=
    measure_ne_top_of_subset (show Set.Ioc (0 : ℝ) R ⊆ Set.Icc 0 R from fun _ hr ↦ ⟨hr.1.le, hr.2⟩)
      isCompact_Icc.measure_ne_top
  have hupper : (∫ r in Set.Ioc 0 R, ∫ ξ in coordinateBox 4, profileEnergy P M r ξ) ≤ R * H := by
    calc
      _ ≤ ∫ r in Set.Ioc 0 R, H := by
        apply setIntegral_mono_on hjoint.integral_prod_left
          (integrableOn_const hfin) measurableSet_Ioc
        intro r hr
        exact (profileEnergy_integral_le_spatial P M hr.1.le).trans
          (cutoffSignal_energy_upper hS hr.1 hr.2 hM hD (fun x ↦ hbound x r hr.1 hr.2))
      _ = R * H := by simp [integral_const, Real.volume_real_Ioc, hRpos.le]
  have h := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 1 / R)
  have heq : (1 / R) * (R * H) = H := by field_simp
  rw [heq] at h
  exact (averaged_profile_energy_lower P M hR).trans h

end DiskDiscrepancy
