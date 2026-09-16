import Mathlib
import Proof.Defs
import Proof.Exp
import Proof.Arith
import Proof.Coeff
import Proof.PowerSums

/-!
# Erdős Problem 494: the Selfridge–Straus uniqueness criteria

Selfridge and Straus (Pacific J. Math. 8 (1958) 847–856) proved that a finite set `A ⊆ ℂ` is
determined by the multiset `A_k` of its `k`-fold sums of distinct elements whenever a prime
`p > k` divides `|A|` (Corollary to Theorem 4), and, for `k = 2`, whenever `|A|` is not a power
of two (Theorem 1).  Both statements are the formal-conjectures variants
`erdos_494.variants.card_divisible_by_prime_gt_k` and `erdos_494.variants.k_eq_2_card_not_pow_two`.

Proof: if `sumMultiset A k = sumMultiset B k` then `sigma A k j = sigma B k j` for all `j`; by
strong induction on `j`, `Coeff.coeff_diff` together with `Exp.coeff_esym` gives
`acoef n j k · (S_j(A) - S_j(B)) = 0`, and the coefficient is nonzero (`Arith`), so all power
sums agree and `PowerSums.eq_of_psum_eq` yields `A = B`.
-/

open Finset

namespace Erdos494

/-- All power sums agree once the `k`-fold sum multisets agree and every coefficient
`acoef n j k` (`j ≥ 1`) is nonzero. -/
theorem psum_eq_of_sumMultiset_eq (A B : Finset ℂ) (k : ℕ) (hcard : A.card = B.card)
    (h : sumMultiset A k = sumMultiset B k) (hne : ∀ j, 1 ≤ j → acoef A.card j k ≠ 0) :
    ∀ j, 1 ≤ j → psum A j = psum B j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hS : ∀ i, 1 ≤ i → i < j → psum A i = psum B i := fun i hi hij => ih i hij hi
    have key := (coeff_diff A B hcard j hj hS k).2
    have hzero : (j.factorial : ℂ) *
        (PowerSeries.coeff j (esym A k) - PowerSeries.coeff j (esym B k)) = 0 := by
      rw [mul_sub, coeff_esym, coeff_esym, sigma_eq_of_sumMultiset_eq h j, sub_self]
    rw [hzero] at key
    exact sub_eq_zero.1
      ((mul_eq_zero.1 key.symm).resolve_left (Int.cast_ne_zero.2 (hne j hj)))

/-- **Selfridge–Straus (1958), Corollary to Theorem 4.** -/
theorem card_divisible_by_prime_gt_k :
    ∀ (k card p : ℕ), p.Prime → k ∈ Set.Ioo 0 p → p ∣ card → Erdos494Unique k card := by
  intro k card p hp hk hdvd A B hA hB h
  obtain ⟨hk0, hkp⟩ := Set.mem_Ioo.1 hk
  refine eq_of_psum_eq A B (hA.trans hB.symm)
    (psum_eq_of_sumMultiset_eq A B k (hA.trans hB.symm) h fun j hj => ?_)
  rw [hA]
  exact acoef_ne_zero_of_prime hp hdvd hk0 hkp hj

/-- **Selfridge–Straus (1958), Theorem 1.** -/
theorem k_eq_2_card_not_pow_two :
    ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494Unique 2 card := by
  intro card hcard A B hA hB h
  refine eq_of_psum_eq A B (hA.trans hB.symm)
    (psum_eq_of_sumMultiset_eq A B 2 (hA.trans hB.symm) h fun j hj => ?_)
  rw [hA]
  exact acoef_two_ne_zero card j hj hcard

/-- `card_divisible_by_prime_gt_k` with every quantifier and hypothesis exposed as a named
binder (the form audited by the MerLean binder census); it is a direct instance of the root. -/
theorem card_divisible_by_prime_gt_k_explicit (k card p : ℕ) (hp : p.Prime)
    (hk : k ∈ Set.Ioo 0 p) (hdvd : p ∣ card) (A B : Finset ℂ) (hA : A.card = card)
    (hB : B.card = card) (h : sumMultiset A k = sumMultiset B k) : A = B :=
  card_divisible_by_prime_gt_k k card p hp hk hdvd A B hA hB h

/-- `k_eq_2_card_not_pow_two` with every quantifier and hypothesis exposed as a named binder. -/
theorem k_eq_2_card_not_pow_two_explicit (card : ℕ) (hcard : ∀ l : ℕ, card ≠ 2 ^ l)
    (A B : Finset ℂ) (hA : A.card = card) (hB : B.card = card)
    (h : sumMultiset A 2 = sumMultiset B 2) : A = B :=
  k_eq_2_card_not_pow_two card hcard A B hA hB h

end Erdos494
