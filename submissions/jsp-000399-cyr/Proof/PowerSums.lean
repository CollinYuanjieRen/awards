import Mathlib
import Proof.Defs

/-!
# Power sums determine a finite set of complex numbers

Two finite sets `A B ⊆ ℂ` of the same cardinality with `∑_{a∈A} a^j = ∑_{b∈B} b^j`
for all `j ≥ 1` are equal: Newton's identities
(`MvPolynomial.psum_eq_mul_esymm_sub_sum`, evaluated at the elements) determine the elementary
symmetric functions from the power sums in characteristic zero,
`Multiset.prod_X_sub_X_eq_sum_esymm` then identifies `∏_{a∈A} (X - C a)` with
`∏_{b∈B} (X - C b)`, and `Polynomial.roots_multiset_prod_X_sub_C` recovers the multisets.
-/

open Finset Polynomial

namespace Erdos494

/-- Evaluating the multivariate power sum at the elements of `A` gives `psum A n`. -/
private theorem eval_mvPsum (A : Finset ℂ) (n : ℕ) :
    MvPolynomial.eval (fun a : ↥A => (a : ℂ)) (MvPolynomial.psum (↥A) ℂ n) = psum A n := by
  simp only [MvPolynomial.psum, psum, map_sum, map_pow, MvPolynomial.eval_X]
  exact Finset.sum_attach A fun a => a ^ n

/-- Evaluating the multivariate elementary symmetric polynomial at the elements of `A` gives
the elementary symmetric function of the multiset `A.val`. -/
private theorem eval_mvEsymm (A : Finset ℂ) (n : ℕ) :
    MvPolynomial.eval (fun a : ↥A => (a : ℂ)) (MvPolynomial.esymm (↥A) ℂ n) =
      A.val.esymm n := by
  rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  congr 1
  exact Multiset.attach_map_val A.val

/-- Newton's identity for the power sums of a finite set of complex numbers. -/
private theorem psum_eq_esymm_sub_sum (A : Finset ℂ) (k : ℕ) (hk : 0 < k) :
    psum A k = (-1) ^ (k + 1) * k * A.val.esymm k -
      ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (-1) ^ a.1 * A.val.esymm a.1 * psum A a.2 := by
  have h := congrArg (MvPolynomial.aeval (fun a : ↥A => (a : ℂ)))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum (↥A) ℂ k hk)
  simpa [eval_mvPsum, eval_mvEsymm] using h

/-- Power sums of positive degree determine all elementary symmetric functions. -/
private theorem esymm_eq_of_psum_eq {A B : Finset ℂ}
    (h : ∀ j, 1 ≤ j → psum A j = psum B j) (k : ℕ) : A.val.esymm k = B.val.esymm k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [Multiset.esymm]
    · have hsum : (∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (-1 : ℂ) ^ a.1 * A.val.esymm a.1 * psum A a.2) =
          ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            (-1 : ℂ) ^ a.1 * B.val.esymm a.1 * psum B a.2 := by
        refine Finset.sum_congr rfl fun a ha => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ha
        have hae := Finset.HasAntidiagonal.mem_antidiagonal.mp h1
        simp only [Set.mem_Ioo] at h2
        rw [ih a.1 h2.2, h a.2 (by omega)]
      have key : (-1 : ℂ) ^ (k + 1) * k * A.val.esymm k =
          (-1 : ℂ) ^ (k + 1) * k * B.val.esymm k := by
        have hpk := h k hk
        rw [psum_eq_esymm_sub_sum A k hk, psum_eq_esymm_sub_sum B k hk, hsum] at hpk
        linear_combination hpk
      have hne : ((-1 : ℂ) ^ (k + 1) * k) ≠ 0 := by
        simp [Nat.cast_ne_zero.mpr hk.ne']
      refine mul_left_cancel₀ hne ?_
      rw [mul_assoc, mul_assoc] at key
      simpa [mul_assoc] using key

/-- Finite sets of complex numbers of equal cardinality with equal power sums of all positive
degrees are equal. -/
theorem eq_of_psum_eq (A B : Finset ℂ) (hcard : A.card = B.card)
    (h : ∀ j, 1 ≤ j → psum A j = psum B j) : A = B := by
  have hesymm := esymm_eq_of_psum_eq h
  have hcv : Multiset.card A.val = Multiset.card B.val := hcard
  have hpoly : (A.val.map fun t => X - C t).prod = (B.val.map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hcv]
    exact Finset.sum_congr rfl fun j _ => by rw [hesymm j]
  have hroots := congrArg Polynomial.roots hpoly
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C,
    Finset.val_inj] at hroots

end Erdos494
