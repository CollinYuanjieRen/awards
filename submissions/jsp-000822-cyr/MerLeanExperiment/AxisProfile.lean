import MerLeanExperiment.ComplexDiskPolar
import MerLeanExperiment.RadialProfile

open MeasureTheory Set
open scoped FourierTransform Real

namespace DiskDiscrepancy

theorem angularKernel_zero : angularKernel 0 = 1 := by
  rw [angularKernel]
  simp
  field_simp [Real.pi_ne_zero]
  norm_num

/-- Scaling of the radial Bessel integral. -/
theorem integral_mul_angularKernel_scaled {c r : ℝ} (hc : c ≠ 0) :
    (∫ s in 0..r, s * angularKernel (c * s)) =
      c⁻¹ ^ 2 * angularPrimitive (c * r) := by
  have hcomp := intervalIntegral.integral_comp_mul_left
    (fun t : ℝ ↦ t * angularKernel t) hc (a := 0) (b := r)
  have hcomp' : (∫ s in 0..r, (c * s) * angularKernel (c * s)) =
      c⁻¹ * angularPrimitive (c * r) := by
    simpa [angularPrimitive] using hcomp
  have hmul : c * (∫ s in 0..r, s * angularKernel (c * s)) =
      ∫ s in 0..r, (c * s) * angularKernel (c * s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [← hmul] at hcomp'
  field_simp [hc] at hcomp' ⊢
  nlinarith

/-- The imaginary-axis Fourier formula normalized as a real interval integral. -/
theorem fourier_complexDiskIndicator_mul_I_eq_integral {r ρ : ℝ} (hr : 0 ≤ r) :
    𝓕 (complexDiskIndicator r) ((ρ : ℂ) * Complex.I) =
      ((2 * Real.pi * ∫ s in 0..r,
        s * angularKernel (2 * Real.pi * ρ * s) : ℝ) : ℂ) := by
  rw [fourier_complexDiskIndicator_mul_I_eq_radial hr]
  rw [← intervalIntegral.integral_of_le hr]
  calc
    (∫ s in 0..r,
        (s : ℂ) * ((2 * Real.pi * angularKernel (2 * Real.pi * ρ * s) : ℝ) : ℂ)) =
        ∫ s in 0..r,
          ((2 * Real.pi * (s * angularKernel (2 * Real.pi * ρ * s)) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro s _
      push_cast
      ring
    _ = ((∫ s in 0..r,
          2 * Real.pi * (s * angularKernel (2 * Real.pi * ρ * s))) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro s _
      push_cast
      rfl
    _ = ((2 * Real.pi * ∫ s in 0..r,
          s * angularKernel (2 * Real.pi * ρ * s) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_const_mul]
      push_cast
      congr 1
      rw [← intervalIntegral.integral_ofReal]
      apply intervalIntegral.integral_congr
      intro s _
      push_cast
      rfl

/-- At nonzero imaginary-axis frequency the actual disk transform equals the
radial profile. -/
theorem fourier_complexDiskIndicator_mul_I_eq_profile {r ρ : ℝ}
    (hr : 0 ≤ r) (hρ : ρ ≠ 0) :
    𝓕 (complexDiskIndicator r) ((ρ : ℂ) * Complex.I) =
      (radialProfile ρ r : ℂ) := by
  rw [fourier_complexDiskIndicator_mul_I_eq_integral hr]
  have hc : 2 * Real.pi * ρ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hρ
  rw [integral_mul_angularKernel_scaled hc]
  simp only [radialProfile, hρ, ↓reduceIte]
  push_cast
  field_simp [hρ, Real.pi_ne_zero]

end DiskDiscrepancy
