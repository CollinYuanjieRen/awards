import Mathlib.Analysis.Fourier.AddCircle

/-! Fourier coefficients under translation on the unit additive circle. -/

namespace Kesten

open AddCircle MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Translating a function on the unit additive circle multiplies its Fourier coefficient by
the corresponding character value. -/
theorem fourierCoeff_translate (F : AddCircle (1 : ℝ) → ℂ) (a : AddCircle (1 : ℝ))
    (k : ℤ) :
    fourierCoeff (fun x ↦ F (x + a)) k = fourier k a * fourierCoeff F k := by
  rw [fourierCoeff, fourierCoeff]
  calc
    ∫ x, fourier (-k) x * F (x + a) ∂haarAddCircle =
        ∫ x, (fourier (-k) (x - a) * F x) ∂haarAddCircle := by
      rw [← integral_add_right_eq_self (fun x ↦ fourier (-k) (x - a) * F x) a]
      congr 1
      funext x
      simp
    _ = fourier k a * ∫ x, fourier (-k) x * F x ∂haarAddCircle := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [fourier_apply, smul_sub, sub_eq_add_neg, toCircle_add, Circle.coe_mul,
        toCircle_neg, Circle.coe_inv_eq_conj]
      simp [fourier_apply, toCircle_neg]
      have ha : ((starRingEnd ℂ) (↑(toCircle (k • a)) : ℂ))⁻¹ = ↑(toCircle (k • a)) := by
        rw [← Circle.coe_inv_eq_conj]
        simp
      rw [ha]
      ring

end Kesten
