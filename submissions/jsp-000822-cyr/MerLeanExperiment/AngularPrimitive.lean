import MerLeanExperiment.AngularBessel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Real
open MeasureTheory intervalIntegral Set

namespace DiskDiscrepancy

/-- The radial primitive of the angular Bessel kernel. -/
noncomputable def angularPrimitive (z : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..z, t * angularKernel t

/-- The primitive is exactly `-z J'(z)`, without any division by `z`. -/
theorem angularPrimitive_eq_neg_mul_deriv (z : ℝ) :
    angularPrimitive z = -z * angularKernelDeriv z := by
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun x : ℝ ↦ -x * angularKernelDeriv x)
      (t * angularKernel t) t := by
    intro t
    have hraw := (hasDerivAt_id t).neg.mul (hasDerivAt_angularKernelDeriv t)
    have hcoef : -1 * angularKernelDeriv t + (-t) *
        angularKernelDeriv2 t = t * angularKernel t := by
      have hode := angularKernel_ode t
      linear_combination -hode
    change HasDerivAt (-id * angularKernelDeriv) (t * angularKernel t) t
    exact hraw.congr_deriv hcoef
  have hint : IntervalIntegrable (fun t : ℝ ↦ t * angularKernel t)
      volume 0 z :=
    (continuous_id.mul continuous_angularKernel).intervalIntegrable _ _
  rw [angularPrimitive,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hderiv t) hint]
  ring

/-- The rescaled angular kernel used in the oscillator energy. -/
noncomputable def angularU (t : ℝ) : ℝ :=
  Real.sqrt t * angularKernel t

/-- The derivative coordinate paired with `angularU`. -/
noncomputable def angularV (t : ℝ) : ℝ :=
  Real.sqrt t * angularKernelDeriv t +
    angularKernel t / (2 * Real.sqrt t)

/-- On the positive axis, `angularV` is the derivative of `angularU`. -/
theorem hasDerivAt_angularU {t : ℝ} (ht : 0 < t) :
    HasDerivAt angularU (angularV t) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsqrt := Real.hasDerivAt_sqrt ht0
  have hraw := hsqrt.mul (hasDerivAt_angularKernel t)
  change HasDerivAt (fun x : ℝ ↦ Real.sqrt x * angularKernel x)
    (Real.sqrt t * angularKernelDeriv t +
      angularKernel t / (2 * Real.sqrt t)) t
  apply hraw.congr_deriv
  field_simp
  ring

/-- The rescaled derivative obeys the nonsingular oscillator equation on the
positive axis. -/
theorem hasDerivAt_angularV {t : ℝ} (ht : 0 < t) :
    HasDerivAt angularV
      (-(1 + 1 / (4 * t ^ 2)) * angularU t) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hs0 : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hsqrt := Real.hasDerivAt_sqrt ht0
  have hfirst := hsqrt.mul (hasDerivAt_angularKernelDeriv t)
  have hdenom : HasDerivAt (fun x : ℝ ↦ 2 * Real.sqrt x)
      (1 / Real.sqrt t) t := by
    apply (hsqrt.const_mul 2).congr_deriv
    field_simp
  have hsecond := (hasDerivAt_angularKernel t).div hdenom
    (by positivity : 2 * Real.sqrt t ≠ 0)
  have hraw := hfirst.add hsecond
  change HasDerivAt
    (fun x : ℝ ↦ Real.sqrt x * angularKernelDeriv x +
      angularKernel x / (2 * Real.sqrt x))
    (-(1 + 1 / (4 * t ^ 2)) *
      (Real.sqrt t * angularKernel t)) t
  have hode := angularKernel_ode t
  have hsquare : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hfour : (Real.sqrt t) ^ 4 = t ^ 2 := by
    calc
      (Real.sqrt t) ^ 4 = ((Real.sqrt t) ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [hsquare]
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  have hJ2 : angularKernelDeriv2 t =
      -angularKernelDeriv t / t - angularKernel t := by
    field_simp [ht0]
    all_goals
      ring_nf at hode ⊢
      linarith
  apply hraw.congr_deriv
  rw [hJ2]
  field_simp [ht0, hs0, ht2]
  rw [hsquare, hfour]
  ring

/-- The initial position has energy contribution between one quarter and one. -/
theorem angularU_one_sq_bounds :
    (1 : ℝ) / 4 ≤ angularU 1 ^ 2 ∧ angularU 1 ^ 2 ≤ 1 := by
  have hlo := one_half_le_angularKernel (t := (1 : ℝ)) (by norm_num) (by norm_num)
  have habs := abs_angularKernel_le_one 1
  rw [angularU]
  norm_num
  constructor
  · nlinarith [sq_nonneg (angularKernel 1 - 1 / 2)]
  · nlinarith [sq_abs (angularKernel 1)]

/-- The initial velocity has squared magnitude at most `9/4`. -/
theorem angularV_one_sq_le : angularV 1 ^ 2 ≤ (9 : ℝ) / 4 := by
  have hJ := abs_angularKernel_le_one 1
  have hJd := abs_angularKernelDeriv_le_one 1
  have hvabs : |angularV 1| ≤ (3 : ℝ) / 2 := by
    rw [angularV]
    norm_num
    calc
      |angularKernelDeriv 1 + angularKernel 1 / 2|
          ≤ |angularKernelDeriv 1| + |angularKernel 1 / 2| := abs_add_le _ _
      _ ≤ 1 + (1 : ℝ) / 2 := by
        exact add_le_add hJd (by
          rw [abs_div]
          simpa using div_le_div_of_nonneg_right hJ
            (by norm_num : (0 : ℝ) ≤ 2))
      _ = 3 / 2 := by norm_num
  nlinarith [sq_abs (angularV 1),
    mul_self_le_mul_self (abs_nonneg (angularV 1)) hvabs]

/-- The primitive is the oscillator velocity combination on the positive axis. -/
theorem angularPrimitive_eq_sqrt_mul {t : ℝ} (ht : 0 < t) :
    angularPrimitive t = Real.sqrt t *
      (angularU t / (2 * t) - angularV t) := by
  rw [angularPrimitive_eq_neg_mul_deriv, angularU, angularV]
  have hs0 : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hsquare : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  field_simp
  rw [hsquare]
  ring

/-- On the unit interval the primitive has its elementary quadratic lower bound. -/
theorem sq_div_four_le_angularPrimitive {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z ^ 2 / 4 ≤ angularPrimitive z := by
  have hmono : (∫ t in (0 : ℝ)..z, t / 2) ≤
      ∫ t in (0 : ℝ)..z, t * angularKernel t := by
    exact intervalIntegral.integral_mono_on hz0
      ((continuous_id.div_const 2).intervalIntegrable _ _)
      ((continuous_id.mul continuous_angularKernel).intervalIntegrable _ _)
      (fun t ht ↦ by
        have hJ := one_half_le_angularKernel ht.1 (le_trans ht.2 hz1)
        nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hJ)])
  rw [angularPrimitive]
  convert hmono using 1
  rw [intervalIntegral.integral_div, integral_id]
  ring

end DiskDiscrepancy
