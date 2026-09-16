import MerLeanExperiment.AngularComplexIntegral
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open MeasureTheory Set
open scoped FourierTransform Real RealInnerProductSpace

namespace DiskDiscrepancy

/-- The actual closed-disk indicator on the complex plane. -/
noncomputable def complexDiskIndicator (r : ℝ) : ℂ → ℂ :=
  (Metric.closedBall (0 : ℂ) r).indicator (fun _ ↦ 1)

/-- The complex closed-disk indicator is integrable. -/
theorem integrable_complexDiskIndicator (r : ℝ) :
    Integrable (complexDiskIndicator r) := by
  unfold complexDiskIndicator
  apply (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
  exact integrableOn_const
    ((isCompact_closedBall (0 : ℂ) r).measure_ne_top)

/-- On polar coordinates, pairing with the imaginary-axis frequency extracts
the sine coordinate. -/
theorem inner_polarCoord_symm_mul_I (p : ℝ × ℝ) (ρ : ℝ) :
    inner ℝ (Complex.polarCoord.symm p) ((ρ : ℂ) * Complex.I) =
      p.1 * ρ * Real.sin p.2 := by
  rw [Complex.inner, Complex.polarCoord_symm_apply]
  simp [Complex.mul_re, Complex.mul_im, -Complex.ofReal_sin]
  ring

/-- The closed-disk condition becomes exactly the radial inequality on the
positive polar target. -/
theorem complexDiskIndicator_polar {r : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Complex.polarCoord.target) :
    complexDiskIndicator r (Complex.polarCoord.symm p) =
      if p.1 ≤ r then 1 else 0 := by
  rw [Complex.polarCoord_target] at hp
  have hp0 : 0 < p.1 := hp.1
  by_cases hpr : p.1 ≤ r
  · simp [hpr, complexDiskIndicator, Metric.mem_closedBall,
      abs_of_pos hp0]
  · simp [hpr, complexDiskIndicator, Metric.mem_closedBall,
      abs_of_pos hp0]

/-- The actual Fourier integrand pulled back to the polar target. -/
theorem polar_fourier_integrand {r ρ : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Complex.polarCoord.target) :
    p.1 • Complex.exp
        (((-2 * Real.pi *
          inner ℝ (Complex.polarCoord.symm p) ((ρ : ℂ) * Complex.I) : ℝ) : ℂ) *
            Complex.I) •
      complexDiskIndicator r (Complex.polarCoord.symm p) =
      if p.1 ≤ r then
        (p.1 : ℂ) * Complex.exp
          (((-2 * Real.pi * ρ * p.1 * Real.sin p.2 : ℝ) : ℂ) * Complex.I)
      else 0 := by
  rw [inner_polarCoord_symm_mul_I, complexDiskIndicator_polar hp]
  rw [Complex.polarCoord_target] at hp
  have hp0 : p.1 ≠ 0 := ne_of_gt hp.1
  by_cases hpr : p.1 ≤ r
  · simp [hpr, hp0, Complex.real_smul]
    ring
  · simp [hpr]

/-- The continuous integrand left after the disk indicator has restricted the
positive radial coordinate to the disk radius. -/
noncomputable def polarRectangleIntegrand (ρ : ℝ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) * Complex.exp
    (((-2 * Real.pi * ρ * p.1 * Real.sin p.2 : ℝ) : ℂ) * Complex.I)

theorem continuous_polarRectangleIntegrand (ρ : ℝ) :
    Continuous (polarRectangleIntegrand ρ) := by
  unfold polarRectangleIntegrand
  fun_prop

/-- The polar rectangle integrand is genuinely integrable on the rectangle
which represents a disk of nonnegative radius. -/
theorem integrableOn_polarRectangleIntegrand {r ρ : ℝ} :
    IntegrableOn (polarRectangleIntegrand ρ)
      (Ioc 0 r ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
  apply ((continuous_polarRectangleIntegrand ρ).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
  intro p hp
  exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩

/-- Fubini on the concrete polar rectangle. -/
theorem integral_polarRectangleIntegrand_prod {r ρ : ℝ} (_hr : 0 ≤ r) :
    (∫ p in Ioc 0 r ×ˢ Ioo (-Real.pi) Real.pi,
        polarRectangleIntegrand ρ p ∂volume.prod volume) =
      ∫ s in Ioc 0 r, ∫ θ in Ioo (-Real.pi) Real.pi,
        polarRectangleIntegrand ρ (s, θ) := by
  exact setIntegral_prod _ integrableOn_polarRectangleIntegrand

/-- Evaluation of each angular slice of the polar rectangle. -/
theorem integral_polarRectangleIntegrand_slice (ρ s : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
        polarRectangleIntegrand ρ (s, θ)) =
      (s : ℂ) * ((2 * Real.pi * angularKernel (2 * Real.pi * ρ * s) : ℝ) : ℂ) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (neg_le_self (le_of_lt Real.pi_pos))]
  unfold polarRectangleIntegrand
  change (∫ θ in -Real.pi..Real.pi, (s : ℂ) * Complex.exp
    (((-2 * Real.pi * ρ * s * Real.sin θ : ℝ) : ℂ) * Complex.I)) = _
  rw [intervalIntegral.integral_const_mul]
  congr 1
  convert angular_complex_integral (2 * Real.pi * ρ * s) using 1
  apply intervalIntegral.integral_congr
  intro θ _
  push_cast
  ring

/-- The fully Fubini-normalized rectangle integral, with the authentic angular
kernel on every radial slice. -/
theorem integral_polarRectangleIntegrand_eq_radial {r ρ : ℝ} (hr : 0 ≤ r) :
    (∫ p in Ioc 0 r ×ˢ Ioo (-Real.pi) Real.pi,
        polarRectangleIntegrand ρ p ∂volume.prod volume) =
      ∫ s in Ioc 0 r,
        (s : ℂ) * ((2 * Real.pi * angularKernel (2 * Real.pi * ρ * s) : ℝ) : ℂ) := by
  rw [integral_polarRectangleIntegrand_prod hr]
  apply integral_congr_ae
  filter_upwards with s
  exact integral_polarRectangleIntegrand_slice ρ s

/-- The actual Fourier transform on the imaginary axis is the polar rectangle
integral.  This is the change-of-variables step with the closed-disk indicator
still present, rather than an assumed polar formula. -/
theorem fourier_complexDiskIndicator_mul_I_eq_rectangle {r ρ : ℝ} :
    𝓕 (complexDiskIndicator r) ((ρ : ℂ) * Complex.I) =
      ∫ p in Ioc 0 r ×ˢ Ioo (-Real.pi) Real.pi,
        polarRectangleIntegrand ρ p ∂volume.prod volume := by
  rw [Real.fourier_eq']
  rw [← Complex.integral_comp_polarCoord_symm]
  have ht : MeasurableSet polarCoord.target := by
    rw [polarCoord_target]
    exact measurableSet_Ioi.prod measurableSet_Ioo
  rw [← integral_indicator ht]
  rw [← integral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
  congr 1
  funext p
  by_cases hp : p ∈ polarCoord.target
  · rw [polarCoord_target] at hp
    rw [indicator_of_mem]
    · rw [polar_fourier_integrand (show p ∈ Complex.polarCoord.target by
        simpa [Complex.polarCoord_target] using hp)]
      by_cases hpr : p.1 ≤ r
      · simp only [hpr, ↓reduceIte]
        rw [indicator_of_mem]
        · rfl
        · exact ⟨⟨hp.1, hpr⟩, hp.2⟩
      · simp only [hpr, ↓reduceIte]
        rw [indicator_of_notMem]
        intro hmem
        exact hpr hmem.1.2
    · simpa [polarCoord_target] using hp
  · rw [indicator_of_notMem hp]
    have hrect : p ∉ Ioc 0 r ×ˢ Ioo (-Real.pi) Real.pi := by
      intro hmem
      apply hp
      rw [polarCoord_target]
      exact ⟨hmem.1.1, hmem.2⟩
    simp [hrect]

/-- Axis-frequency polar/Fubini normalization through the own angular kernel. -/
theorem fourier_complexDiskIndicator_mul_I_eq_radial {r ρ : ℝ} (hr : 0 ≤ r) :
    𝓕 (complexDiskIndicator r) ((ρ : ℂ) * Complex.I) =
      ∫ s in Ioc 0 r,
        (s : ℂ) * ((2 * Real.pi * angularKernel (2 * Real.pi * ρ * s) : ℝ) : ℂ) := by
  rw [fourier_complexDiskIndicator_mul_I_eq_rectangle,
    integral_polarRectangleIntegrand_eq_radial hr]

end DiskDiscrepancy
