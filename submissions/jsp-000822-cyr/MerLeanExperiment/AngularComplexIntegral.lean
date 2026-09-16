import MerLeanExperiment.AngularPrimitive
import Mathlib.Analysis.Complex.Trigonometric

open scoped Real
open MeasureTheory intervalIntegral

namespace DiskDiscrepancy

/-- The sine part of the angular exponential is odd and has zero symmetric integral. -/
theorem integral_sin_neg_mul_sin_eq_zero (b : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.sin (-b * Real.sin θ)) = 0 := by
  let g : ℝ → ℝ := fun θ ↦ Real.sin (-b * Real.sin θ)
  have hcomp := intervalIntegral.integral_comp_neg
    (f := g) (a := -Real.pi) (b := Real.pi)
  have hneg : (∫ θ in (-Real.pi)..Real.pi, g (-θ)) =
      -(∫ θ in (-Real.pi)..Real.pi, g θ) := by
    rw [intervalIntegral.integral_congr (g := fun θ ↦ -g θ) (fun θ _ ↦ by
      dsimp [g]
      rw [show -b * Real.sin (-θ) = -(-b * Real.sin θ) by
        rw [Real.sin_neg]
        ring, Real.sin_neg])]
    exact intervalIntegral.integral_neg
  have heq : -(∫ θ in (-Real.pi)..Real.pi, g θ) =
      ∫ θ in (-Real.pi)..Real.pi, g θ := by
    rw [← hneg, hcomp]
    ring_nf
  dsimp [g] at heq ⊢
  linarith

/-- The complete angular complex exponential is the real Bessel average. -/
theorem angular_complex_integral (b : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi,
      Complex.exp (((-b * Real.sin θ : ℝ) : ℂ) * Complex.I)) =
      ((2 * Real.pi * angularKernel b : ℝ) : ℂ) := by
  have hcos : IntervalIntegrable
      (fun θ : ℝ ↦ (Real.cos (-b * Real.sin θ) : ℂ)) volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous fun θ : ℝ ↦
        (Real.cos (-b * Real.sin θ) : ℂ)).intervalIntegrable _ _
  have hsin : IntervalIntegrable
      (fun θ : ℝ ↦ (Real.sin (-b * Real.sin θ) : ℂ) * Complex.I) volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous fun θ : ℝ ↦
        (Real.sin (-b * Real.sin θ) : ℂ) * Complex.I).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ ↦
    (Real.cos (-b * Real.sin θ) : ℂ) +
      (Real.sin (-b * Real.sin θ) : ℂ) * Complex.I) (fun θ _ ↦ by
        exact Complex.exp_ofReal_mul_I _)]
  rw [intervalIntegral.integral_add hcos hsin,
    intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal,
    integral_sin_neg_mul_sin_eq_zero, Complex.ofReal_zero, zero_mul, add_zero]
  rw [angularKernel]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp
  rw [Real.cos_neg]

end DiskDiscrepancy
