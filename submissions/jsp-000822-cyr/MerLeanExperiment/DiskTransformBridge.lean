import MerLeanExperiment.AxisProfile
import MerLeanExperiment.DiskFourier
import Mathlib.Analysis.Complex.Isometry

open MeasureTheory Set
open scoped FourierTransform Real

namespace DiskDiscrepancy

noncomputable abbrev planeComplexIsometry : Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- The plane disk indicator is the complex disk indicator transported through
its canonical orthonormal coordinates. -/
theorem diskIndicator_eq_complex_comp (r : ℝ) :
    diskIndicator r = complexDiskIndicator r ∘ planeComplexIsometry := by
  funext x
  simp only [diskIndicator, complexDiskIndicator, Function.comp_apply]
  by_cases hx : x ∈ Metric.closedBall (0 : Plane) r
  · rw [indicator_of_mem hx, indicator_of_mem]
    rw [Metric.mem_closedBall, dist_zero_right, planeComplexIsometry.norm_map]
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  · rw [indicator_of_notMem hx, indicator_of_notMem]
    intro h
    apply hx
    rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
    rw [planeComplexIsometry.norm_map] at h
    exact h

/-- The actual complex disk transform depends only on the norm of a nonzero
frequency, by an explicit unit rotation to the imaginary axis. -/
theorem fourier_complexDiskIndicator_eq_axis {r : ℝ} (ζ : ℂ) (hζ : ζ ≠ 0) :
    𝓕 (complexDiskIndicator r) ζ =
      𝓕 (complexDiskIndicator r) (((‖ζ‖ : ℝ) : ℂ) * Complex.I) := by
  have hρ : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.mpr hζ
  have hρpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  let a : Circle := ⟨ζ / (((‖ζ‖ : ℝ) : ℂ) * Complex.I), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [Complex.norm_real, hρ]⟩
  have ha : rotation a (((‖ζ‖ : ℝ) : ℂ) * Complex.I) = ζ := by
    rw [rotation_apply]
    dsimp [a]
    apply div_mul_cancel₀
    exact mul_ne_zero (by exact_mod_cast hρ) Complex.I_ne_zero
  have hinv : complexDiskIndicator r ∘ rotation a = complexDiskIndicator r := by
    funext z
    unfold complexDiskIndicator
    simp only [Function.comp_apply]
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) r
    · rw [indicator_of_mem hz, indicator_of_mem]
      simpa [Metric.mem_closedBall, Circle.norm_coe] using hz
    · rw [indicator_of_notMem hz, indicator_of_notMem]
      intro h
      apply hz
      simpa [Metric.mem_closedBall, Circle.norm_coe] using h
  have hcov := Real.fourier_comp_linearIsometry (rotation a)
    (complexDiskIndicator r) (((‖ζ‖ : ℝ) : ℂ) * Complex.I)
  rw [hinv, ha] at hcov
  exact hcov.symm

/-- The actual complex disk transform is the compiled radial profile. -/
theorem fourier_complexDiskIndicator_eq_profile {r : ℝ} (hr : 0 ≤ r) (ζ : ℂ) :
    𝓕 (complexDiskIndicator r) ζ = (radialProfile ‖ζ‖ r : ℂ) := by
  by_cases hζ : ζ = 0
  · subst ζ
    simp only [norm_zero, radialProfile, ↓reduceIte]
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) * Complex.I by simp]
    rw [fourier_complexDiskIndicator_mul_I_eq_integral hr]
    simp [angularKernel_zero]
    ring
  · rw [fourier_complexDiskIndicator_eq_axis ζ hζ]
    exact fourier_complexDiskIndicator_mul_I_eq_profile hr
      (norm_ne_zero_iff.mpr hζ)

/-- Pointwise Fourier transform formula for the actual plane disk indicator. -/
theorem fourier_diskIndicator_eq_profile {r : ℝ} (hr : 0 ≤ r) (ξ : Plane) :
    𝓕 (diskIndicator r) ξ = (radialProfile ‖ξ‖ r : ℂ) := by
  rw [diskIndicator_eq_complex_comp]
  rw [Real.fourier_comp_linearIsometry]
  rw [fourier_complexDiskIndicator_eq_profile hr]
  congr 2
  exact planeComplexIsometry.norm_map ξ

end DiskDiscrepancy
