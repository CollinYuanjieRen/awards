import Mathlib
import Proof.Defs

/-!
# Exponential generating functions

For `a : ℂ` let `E a = exp (a x) ∈ ℂ⟦x⟧`.  Since `E a * E b = E (a + b)`, the elementary
symmetric function `esym A m = ∑_{T ⊆ A, |T| = m} ∏_{a ∈ T} E a` equals `∑_T E (∑ T)`, whose
`j`-th coefficient is `sigma A m j / j!`; the power sum `pw A i = ∑_{a ∈ A} (E a)^i` has `j`-th
coefficient `i^j · psum A j / j!`.  Newton's identity
`m · esym A m = ∑_{i=1}^{m} (-1)^(i-1) esym A (m-i) * pw A i` holds in `ℂ⟦x⟧`.
-/

open Finset PowerSeries

namespace Erdos494

/-- `E a = exp (a · x)` as a formal power series over `ℂ`. -/
noncomputable def E (a : ℂ) : PowerSeries ℂ := PowerSeries.rescale a (PowerSeries.exp ℂ)

theorem E_mul (a b : ℂ) : E a * E b = E (a + b) :=
  PowerSeries.exp_mul_exp_eq_exp_add a b

theorem E_zero : E 0 = 1 := by
  simp [E]

theorem prod_E (T : Finset ℂ) : ∏ a ∈ T, E a = E (∑ a ∈ T, a) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [E_zero]
  | insert a T ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, E_mul]

theorem E_pow (a : ℂ) (i : ℕ) : E a ^ i = E (i * a) := by
  induction i with
  | zero => simpa using E_zero.symm
  | succ i ih =>
    rw [pow_succ, ih, E_mul]
    congr 1
    push_cast
    ring

theorem coeff_E (a : ℂ) (j : ℕ) : PowerSeries.coeff j (E a) = a ^ j / (j.factorial : ℂ) := by
  simp [E, PowerSeries.coeff_rescale, div_eq_mul_inv]

/-- The `m`-th elementary symmetric function of the exponentials `E a`, `a ∈ A`. -/
noncomputable def esym (A : Finset ℂ) (m : ℕ) : PowerSeries ℂ :=
  ∑ T ∈ A.powersetCard m, ∏ a ∈ T, E a

/-- The `i`-th power sum of the exponentials `E a`, `a ∈ A`. -/
noncomputable def pw (A : Finset ℂ) (i : ℕ) : PowerSeries ℂ := ∑ a ∈ A, E a ^ i

theorem esym_zero (A : Finset ℂ) : esym A 0 = 1 := by
  simp [esym]

theorem coeff_esym (A : Finset ℂ) (m j : ℕ) :
    (j.factorial : ℂ) * PowerSeries.coeff j (esym A m) = sigma A m j := by
  have hj : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
  simp only [esym, map_sum, prod_E, coeff_E, Finset.mul_sum, sigma]
  exact Finset.sum_congr rfl fun T _ => mul_div_cancel₀ _ hj

theorem coeff_zero_esym (A : Finset ℂ) (m : ℕ) :
    PowerSeries.coeff 0 (esym A m) = (A.card.choose m : ℂ) := by
  simp [esym, map_sum, prod_E, coeff_E, Finset.card_powersetCard]

theorem coeff_pw (A : Finset ℂ) (i j : ℕ) :
    (j.factorial : ℂ) * PowerSeries.coeff j (pw A i) = (i : ℂ) ^ j * psum A j := by
  have hj : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
  simp only [pw, E_pow, map_sum, coeff_E, Finset.mul_sum, psum, mul_pow]
  exact Finset.sum_congr rfl fun a _ => mul_div_cancel₀ _ hj

theorem coeff_zero_pw (A : Finset ℂ) (i : ℕ) : PowerSeries.coeff 0 (pw A i) = (A.card : ℂ) := by
  simp [pw, E_pow, map_sum, coeff_E]

/-- Newton's identity for the exponentials `E a`, `a ∈ A`. -/
theorem newton (A : Finset ℂ) (m : ℕ) (_hm : 1 ≤ m) :
    (m : PowerSeries ℂ) * esym A m =
      ∑ i ∈ Finset.Icc 1 m, (-1 : PowerSeries ℂ) ^ (i - 1) * (esym A (m - i) * pw A i) := by
  classical
  have hmap : ((Finset.univ : Finset {x // x ∈ A}).val.map fun a : {x // x ∈ A} => E (a : ℂ))
      = A.val.map E := by
    rw [← Finset.attach_eq_univ, Finset.attach_val]
    exact Multiset.attach_map_val' A.val E
  have hesym : ∀ n : ℕ, MvPolynomial.aeval (fun a : {x // x ∈ A} => E (a : ℂ))
      (MvPolynomial.esymm {x // x ∈ A} ℂ n) = esym A n := by
    intro n
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hmap, Finset.esymm_map_val]
    rfl
  have hpw : ∀ i : ℕ, MvPolynomial.aeval (fun a : {x // x ∈ A} => E (a : ℂ))
      (MvPolynomial.psum {x // x ∈ A} ℂ i) = pw A i := by
    intro i
    rw [MvPolynomial.psum, map_sum, pw, ← Finset.sum_coe_sort A fun a => E a ^ i]
    exact Finset.sum_congr rfl fun a _ => by rw [map_pow, MvPolynomial.aeval_X]
  have key := congrArg (MvPolynomial.aeval (fun a : {x // x ∈ A} => E (a : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum {x // x ∈ A} ℂ m)
  simp only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, hesym, hpw] at key
  rw [key, Finset.mul_sum]
  refine (Finset.sum_nbij' (fun i => (m - i, i)) (fun a => a.2) ?_ ?_ ?_ ?_ ?_).symm
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    simp only [Finset.mem_Icc]
    omega
  · intro i _
    rfl
  · intro a ha
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    have : m - a.2 = a.1 := by omega
    simp [this]
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    have h : ((-1 : PowerSeries ℂ)) ^ (m + 1) * (-1) ^ (m - i) = (-1) ^ (i - 1) := by
      rw [← pow_add, show m + 1 + (m - i) = (i - 1) + 2 * (m + 1 - i) by omega, pow_add, pow_mul,
        neg_one_sq, one_pow, mul_one]
    dsimp only
    rw [← h]
    ring

end Erdos494
