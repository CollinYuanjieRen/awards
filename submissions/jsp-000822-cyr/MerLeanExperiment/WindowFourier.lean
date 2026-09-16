import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import MerLeanExperiment.SincKernel

open MeasureTheory
open scoped FourierTransform

namespace DiskDiscrepancy

/-- The complex-valued indicator of a centred interval of length `a`. -/
noncomputable def intervalWindow (a : ℝ) : ℝ → ℂ :=
  (Set.Icc (-a / 2) (a / 2)).indicator (fun _ ↦ 1)

theorem interval_fourier_exp_eq_sinc {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ t in (-a / 2)..(a / 2),
      Complex.exp (((-2 * Real.pi * x * t : ℝ) : ℂ) * Complex.I)) =
        ((a * Real.sinc (Real.pi * a * x) : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · simp [hx]
    ring
  let z : ℝ := Real.pi * a * x
  let c : ℂ := ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I
  have hz : z ≠ 0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero ha.ne') hx
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx)) Complex.I_ne_zero
  have hphase (t : ℝ) :
      (((-2 * Real.pi * x * t : ℝ) : ℂ) * Complex.I) = c * t := by
    dsimp [c]
    push_cast
    ring
  simp_rw [hphase]
  rw [integral_exp_mul_complex hc]
  have hright : c * ((a / 2 : ℝ) : ℂ) = ((-z : ℝ) : ℂ) * Complex.I := by
    dsimp [c, z]
    push_cast
    ring
  have hleft : c * ((-a / 2 : ℝ) : ℂ) = (z : ℂ) * Complex.I := by
    dsimp [c, z]
    push_cast
    ring
  rw [hright, hleft, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  rw [show Real.pi * a * x = z from rfl, Real.sinc_of_ne_zero hz]
  push_cast
  dsimp [c, z]
  field_simp [Real.pi_ne_zero, ha.ne', hx, Complex.I_ne_zero]
  push_cast
  ring

theorem integrable_intervalWindow (a : ℝ) :
    Integrable (intervalWindow a) := by
  unfold intervalWindow
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact continuous_const.integrableOn_Icc

/-- The ordinary Fourier transform of the actual interval indicator. -/
theorem fourier_intervalWindow {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕 (intervalWindow a) x = ((a * Real.sinc (Real.pi * a * x) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  simp_rw [Real.inner_apply, smul_eq_mul]
  have hind (f : ℝ → ℂ) : (fun t ↦ f t * intervalWindow a t) =
      (Set.Icc (-a / 2) (a / 2)).indicator f := by
    funext t
    by_cases ht : t ∈ Set.Icc (-a / 2) (a / 2) <;> simp [intervalWindow, ht]
  rw [hind]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a / 2 ≤ a / 2)]
  simpa only [mul_one, mul_assoc, mul_left_comm, mul_comm] using
    interval_fourier_exp_eq_sinc ha x

end DiskDiscrepancy
