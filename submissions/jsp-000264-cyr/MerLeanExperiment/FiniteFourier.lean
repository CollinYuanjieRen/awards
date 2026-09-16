import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace ReciprocalSquares

noncomputable section

def bernWeight (D S : Finset ℕ) (p : ℝ) : ℝ :=
  p ^ S.card * (1 - p) ^ (D \ S).card

def modularProduct {m : ℕ} [NeZero m]
    (D : Finset ℕ) (a : ℕ → ZMod m) (b : ZMod m)
    (p : ℝ) (h : ZMod m) : ℂ :=
  ZMod.stdAddChar (-h * b) *
    ∏ d ∈ D, ((p : ℂ) * ZMod.stdAddChar (h * a d) + (1 - (p : ℂ)))

theorem sum_stdAddChar_mul {m : ℕ} [NeZero m] (a : ZMod m) :
    (∑ h : ZMod m, ZMod.stdAddChar (h * a)) =
      if a = 0 then (m : ℂ) else 0 := by
  simpa only [ZMod.card, apply_ite, Nat.cast_zero] using
    AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar m)

theorem stdAddChar_sum {m : ℕ} [NeZero m]
    (S : Finset ℕ) (a : ℕ → ZMod m) :
    ZMod.stdAddChar (∑ d ∈ S, a d) = ∏ d ∈ S, ZMod.stdAddChar (a d) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert d S hd ih =>
    simp only [Finset.sum_insert hd, Finset.prod_insert hd,
      AddChar.map_add_eq_mul, ih]

/-- The weighted subset expansion before applying character orthogonality. -/
theorem modularProduct_expand {m : ℕ} [NeZero m]
    (D : Finset ℕ) (a : ℕ → ZMod m) (b : ZMod m)
    (p : ℝ) (h : ZMod m) :
    modularProduct D a b p h =
      ∑ S ∈ D.powerset, (bernWeight D S p : ℂ) *
        ZMod.stdAddChar (h * ((∑ d ∈ S, a d) - b)) := by
  classical
  unfold modularProduct
  rw [Finset.prod_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  have hchar : ZMod.stdAddChar (-h * b) *
      (∏ d ∈ S, ZMod.stdAddChar (h * a d)) =
      ZMod.stdAddChar (h * ((∑ d ∈ S, a d) - b)) := by
    rw [← stdAddChar_sum, ← Finset.mul_sum, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [Finset.prod_mul_distrib, Finset.prod_const, bernWeight,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  calc
    _ = ((p : ℂ) ^ S.card * (1 - (p : ℂ)) ^ (D \ S).card) *
        (ZMod.stdAddChar (-h * b) *
          ∏ d ∈ S, ZMod.stdAddChar (h * a d)) := by ring
    _ = _ := by rw [hchar]

/-- Orthogonality converts the character sum to the total weight of the
subsets with the specified modular sum. -/
theorem sum_modularProduct {m : ℕ} [NeZero m]
    (D : Finset ℕ) (a : ℕ → ZMod m) (b : ZMod m) (p : ℝ) :
    (∑ h : ZMod m, modularProduct D a b p h) =
      (m : ℂ) *
        ((∑ S ∈ D.powerset.filter (fun S => (∑ d ∈ S, a d) = b),
          bernWeight D S p : ℝ) : ℂ) := by
  classical
  simp_rw [modularProduct_expand]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_stdAddChar_mul, sub_eq_zero]
  rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp_all [mul_comm]

end
end ReciprocalSquares
