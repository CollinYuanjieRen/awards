import MerLeanExperiment.CenteredProduct
import MerLeanExperiment.FiniteFourier
import MerLeanExperiment.RationalNumerator
import Mathlib.Data.ZMod.ValMinAbs

namespace ReciprocalSquares

noncomputable def centeredProduct (D : Finset ℕ) (p : ℝ) (h : ℤ) : ℂ :=
  ∏ d ∈ D, centeredFactor p (2 * Real.pi * (h : ℝ) / (d : ℝ))

theorem stdAddChar_mul_div (m d : ℕ) [NeZero m] (h : ZMod m)
    (hd : 0 < d) (hdiv : d ∣ m) :
    ZMod.stdAddChar (h * ((m / d : ℕ) : ZMod m)) =
      Complex.exp (((2 * Real.pi * (h.valMinAbs : ℝ) / (d : ℝ) : ℝ) : ℂ) *
        Complex.I) := by
  have hc : h * ((m / d : ℕ) : ZMod m) =
      ((h.valMinAbs * ((m / d : ℕ) : ℤ) : ℤ) : ZMod m) := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.coe_valMinAbs]
  rw [hc, ZMod.stdAddChar_coe]
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  simp only [Int.cast_mul, Int.cast_natCast, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_intCast,
    Complex.ofReal_natCast]
  rw [Nat.cast_div hdiv hdc]
  congr 1
  field_simp

theorem stdAddChar_neg_mul_target (m k : ℕ) [NeZero m] (h : ZMod m)
    (r : ℚ) (hk : (k : ℚ) = (m : ℚ) * r) :
    ZMod.stdAddChar (-h * (k : ZMod m)) =
      Complex.exp (((-2 * Real.pi * (h.valMinAbs : ℝ) * (r : ℝ) : ℝ) : ℂ) *
        Complex.I) := by
  have hc : -h * (k : ZMod m) = ((-h.valMinAbs * (k : ℤ) : ℤ) : ZMod m) := by
    simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast, ZMod.coe_valMinAbs]
  rw [hc, ZMod.stdAddChar_coe]
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hkc : (k : ℂ) = (m : ℂ) * (r : ℂ) := by exact_mod_cast hk
  push_cast
  rw [hkc]
  congr 1
  field_simp

theorem centeredProduct_eq_modularProduct
    (D : Finset ℕ) (m k : ℕ) [NeZero m] (r : ℚ) (p : ℝ)
    (hD : ∀ d ∈ D, 0 < d) (hdiv : ∀ d ∈ D, d ∣ m)
    (hk : (k : ℚ) = (m : ℚ) * r)
    (hp : p * (recipSumQ D : ℝ) = (r : ℝ)) (h : ZMod m) :
    centeredProduct D p h.valMinAbs =
      modularProduct D (fun d => ((m / d : ℕ) : ZMod m)) (k : ZMod m) p h := by
  have hsum : (∑ d ∈ D, 2 * Real.pi * (h.valMinAbs : ℝ) / (d : ℝ)) =
      2 * Real.pi * (h.valMinAbs : ℝ) * (recipSumQ D : ℝ) := by
    simp only [recipSumQ, Rat.cast_sum, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hphase : -p * (∑ d ∈ D, 2 * Real.pi * (h.valMinAbs : ℝ) / (d : ℝ)) =
      -2 * Real.pi * (h.valMinAbs : ℝ) * (r : ℝ) := by
    calc
      _ = -2 * Real.pi * (h.valMinAbs : ℝ) * (p * (recipSumQ D : ℝ)) := by
        rw [hsum]
        ring
      _ = _ := by rw [hp]
  unfold centeredProduct
  rw [prod_centeredFactor_factor, hphase]
  unfold modularProduct
  rw [stdAddChar_neg_mul_target m k h r hk]
  congr 1
  apply Finset.prod_congr rfl
  intro d hd
  rw [stdAddChar_mul_div m d h (hD d hd) (hdiv d hd)]
  push_cast
  ring

end ReciprocalSquares
