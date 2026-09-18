import MerLeanExperiment.AlgebraicSetup
import MerLeanExperiment.ExteriorDisk
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Exterior-root product identities

This module begins the algebraic content of Luo--Yang--Zhu Lemma 3.2.  It
relates `F_z(w) = product_j (1-z_j w)` to the monic product whose roots are the
reciprocals in the closed unit disk.
-/

open Finset Polynomial

namespace Erdos973

theorem one_sub_mul_eq_neg_mul_sub_inv {z w : ℂ} (hz : z ≠ 0) :
    1 - z * w = (-z) * (w - z⁻¹) := by
  calc
    1 - z * w = z * z⁻¹ - z * w := by rw [mul_inv_cancel₀ hz]
    _ = (-z) * (w - z⁻¹) := by ring

/-- The product identity used to rewrite the logarithmic derivative in terms
of the reciprocal roots. -/
theorem eval_rootProduct_eq_reciprocal_product {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ j, 1 ≤ ‖z j‖) (w : ℂ) :
    (rootProduct z).eval w =
      (-1 : ℂ) ^ n * (∏ j, z j) * ∏ j, (w - (z j)⁻¹) := by
  rw [eval_rootProduct]
  have hz0 : ∀ j, z j ≠ 0 := by
    intro j hzero
    have h := hz j
    rw [hzero, norm_zero] at h
    norm_num at h
  simp_rw [one_sub_mul_eq_neg_mul_sub_inv (hz0 _)]
  rw [Finset.prod_mul_distrib]
  simp only [prod_neg, card_univ, Fintype.card_fin]

/-- The monic product with the reciprocal roots. -/
noncomputable def reciprocalProduct {n : ℕ} (z : Fin n → ℂ) (w : ℂ) : ℂ :=
  ∏ j, (w - (z j)⁻¹)

/-- The logarithmic derivative of the reciprocal-root product is the finite
Cauchy transform sum. -/
theorem logDeriv_reciprocalProduct {n : ℕ} (z : Fin n → ℂ) (w : ℂ)
    (hw : ∀ j, w ≠ (z j)⁻¹) :
    logDeriv (reciprocalProduct z) w = ∑ j, (w - (z j)⁻¹)⁻¹ := by
  rw [show reciprocalProduct z = ∏ j : Fin n, (fun w : ℂ => w - (z j)⁻¹) by
    funext u
    simp [reciprocalProduct]]
  rw [logDeriv_prod]
  · simp [logDeriv_apply]
  · intro j _
    exact sub_ne_zero.mpr (hw j)
  · intro j _
    fun_prop

/-- The logarithmic derivative of the original root-product polynomial is the
same reciprocal resolvent sum. -/
theorem logDeriv_eval_rootProduct {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ j, 1 ≤ ‖z j‖) (w : ℂ) (hw : ∀ j, w ≠ (z j)⁻¹) :
    logDeriv (fun u => (rootProduct z).eval u) w =
      ∑ j, (w - (z j)⁻¹)⁻¹ := by
  let A : ℂ := (-1 : ℂ) ^ n * ∏ j, z j
  have hz0 : ∀ j, z j ≠ 0 := by
    intro j hzero
    have h := hz j
    rw [hzero, norm_zero] at h
    norm_num at h
  have hA : A ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hz0 j
  have hfun : (fun u => (rootProduct z).eval u) =
      fun u => A * reciprocalProduct z u := by
    funext u
    simpa [A, reciprocalProduct] using
      eval_rootProduct_eq_reciprocal_product z hz u
  rw [hfun, logDeriv_const_mul w A hA]
  exact logDeriv_reciprocalProduct z w hw

end Erdos973
