import MerLeanExperiment.RadialBounds
import MerLeanExperiment.CutoffUpper

open MeasureTheory

namespace DiskDiscrepancy

open scoped FourierTransform

noncomputable def cutoffSpectrum (P : Finset Plane) (M : ℝ) (ξ : Plane) : ℂ :=
  atomicFourier P ξ - (𝓕 (fun y : Plane ↦ (boxDensity M y : ℂ)) : Plane → ℂ) ξ

theorem continuous_cutoffSpectrum (P : Finset Plane) (M : ℝ) : Continuous (cutoffSpectrum P M) :=
  (continuous_atomicFourier P).sub (continuous_classicalFourier (integrable_boxDensity M).ofReal)

theorem norm_cutoffSpectrum_le (P : Finset Plane) (M : ℝ) (ξ : Plane) :
    ‖cutoffSpectrum P M ξ‖ ≤ P.card + ∫ y : Plane, ‖(boxDensity M y : ℂ)‖ :=
  (norm_sub_le _ _).trans (add_le_add (norm_atomicFourier_le P ξ) (norm_classicalFourier_le _ ξ))

noncomputable def profileEnergy (P : Finset Plane) (M : ℝ) (r : ℝ) (ξ : Plane) : ℝ :=
  ‖cutoffSpectrum P M ξ‖ ^ 2 * radialProfile ‖ξ‖ r ^ 2

theorem measurable_profileEnergy (P : Finset Plane) (M : ℝ) :
    Measurable (fun q : ℝ × Plane ↦ profileEnergy P M q.1 q.2) := by
  apply Measurable.mul
    (((continuous_cutoffSpectrum P M).measurable.comp measurable_snd).norm.pow_const 2)
  exact (measurable_radialProfile.comp
    (measurable_snd.norm.prodMk measurable_fst)).pow_const 2

theorem integrable_profileEnergy (P : Finset Plane) (M : ℝ) {R : ℝ} (_hR : 0 < R) :
    Integrable (fun q : ℝ × Plane ↦ profileEnergy P M q.1 q.2)
      ((volume.restrict (Set.Ioc 0 R)).prod (volume.restrict (coordinateBox 4))) := by
  rw [Measure.prod_restrict]
  have hsub : Set.Ioc (0 : ℝ) R ⊆ Set.Icc 0 R := fun _ hx ↦ ⟨hx.1.le, hx.2⟩
  have hfinite : (volume.prod (volume : Measure Plane))
      (Set.Ioc 0 R ×ˢ coordinateBox 4) ≠ ⊤ :=
    measure_ne_top_of_subset (Set.prod_mono hsub (Set.Subset.refl (coordinateBox 4)))
      (isCompact_Icc.prod (isCompact_coordinateBox 4)).measure_ne_top
  apply Measure.integrableOn_of_bounded hfinite (measurable_profileEnergy P M).aestronglyMeasurable
    (M := (P.card + ∫ y : Plane, ‖(boxDensity M y : ℂ)‖) ^ 2 * (Real.pi * R ^ 2) ^ 2)
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod (isClosed_coordinateBox 4).measurableSet)] with q hq
  have hr0 : 0 ≤ q.1 := hq.1.1.le
  have hrR : q.1 ≤ R := hq.1.2
  have hprofile : |radialProfile ‖q.2‖ q.1| ≤ Real.pi * R ^ 2 :=
    (abs_radialProfile_le_area (norm_nonneg _) hr0).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrR 2) Real.pi_pos.le)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (norm_cutoffSpectrum_le P M q.2) 2
  have hp := pow_le_pow_left₀ (abs_nonneg _) hprofile 2
  simp only [sq_abs] at hp
  change |‖cutoffSpectrum P M q.2‖ ^ 2 * radialProfile ‖q.2‖ q.1 ^ 2| ≤ _
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact mul_le_mul hs hp (sq_nonneg _) (sq_nonneg _)

/-- Genuine Fubini on a finite radius-frequency rectangle yields the averaged spectral lower bound. -/
theorem averaged_profile_energy_lower (P : Finset Plane) (M : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    (8 * radialProfileConstant / 343) * R * P.card ≤
      (1 / R) * ∫ r in Set.Ioc 0 R, ∫ ξ in coordinateBox 4, profileEnergy P M r ξ := by
  have hRpos : 0 < R := by linarith
  have hc := radialProfileConstant_pos
  have hjoint := integrable_profileEnergy P M hRpos
  have hspec : IntegrableOn (fun ξ : Plane ↦ ‖cutoffSpectrum P M ξ‖ ^ 2) (coordinateBox 4) :=
    (continuous_cutoffSpectrum P M).norm.pow 2 |>.continuousOn.integrableOn_compact (isCompact_coordinateBox 4)
  have hlow := finite_square_spectral_lower P M
  have hscale := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ radialProfileConstant / 343 * R)
  calc
    _ = (radialProfileConstant / 343 * R) * (8 * P.card) := by ring
    _ ≤ (radialProfileConstant / 343 * R) * ∫ ξ in coordinateBox 4, ‖cutoffSpectrum P M ξ‖ ^ 2 := hscale
    _ = ∫ ξ in coordinateBox 4, (radialProfileConstant / 343 * R) * ‖cutoffSpectrum P M ξ‖ ^ 2 :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ ξ in coordinateBox 4, (1 / R) * ∫ r in Set.Ioc 0 R, profileEnergy P M r ξ := by
      apply setIntegral_mono_on (hspec.const_mul _) (hjoint.integral_prod_right.const_mul _)
        (isClosed_coordinateBox 4).measurableSet
      intro ξ hξ
      have h := radialProfile_average_lower_on_box hR hξ
      rw [intervalIntegral.integral_of_le hRpos.le] at h
      have hs := mul_le_mul_of_nonneg_left h (sq_nonneg ‖cutoffSpectrum P M ξ‖)
      simp only [profileEnergy, integral_const_mul]
      nlinarith [hs]
    _ = (1 / R) * ∫ ξ in coordinateBox 4, ∫ r in Set.Ioc 0 R, profileEnergy P M r ξ :=
      integral_const_mul _ _
    _ = _ := congrArg (fun t : ℝ ↦ (1 / R) * t) (integral_integral_swap hjoint).symm

end DiskDiscrepancy
