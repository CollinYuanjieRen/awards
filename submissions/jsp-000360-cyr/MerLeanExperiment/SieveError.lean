import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Tactic

namespace Erdos441

/-- The elementary finite sieve error bound, with explicit intersection estimates. -/
theorem sieve_discrepancy_bound {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (bad : ι → Finset α) (L : ℚ) (rho err : ι → ℚ)
    (herr : ∀ T : Finset ι,
      |((T.inf bad).card : ℚ) - L * ∏ i ∈ T, rho i| ≤ ∏ i ∈ T, err i) :
    |(((Finset.univ : Finset ι).inf fun i => (bad i)ᶜ).card : ℚ) -
      L * ∏ i, (1 - rho i)| ≤ ∏ i, (1 + err i) := by
  classical
  have hIE : (((Finset.univ : Finset ι).inf fun i => (bad i)ᶜ).card : ℚ) =
      ∑ T ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℚ) ^ T.card * (T.inf bad).card := by
    exact_mod_cast Finset.inclusion_exclusion_card_inf_compl
      (Finset.univ : Finset ι) bad
  have hprod : (∏ i, (1 - rho i)) =
      ∑ T ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℚ) ^ T.card * ∏ i ∈ T, rho i := by
    simpa using Finset.prod_sub (fun _ : ι => (1 : ℚ)) rho Finset.univ
  have heq : (((Finset.univ : Finset ι).inf fun i => (bad i)ᶜ).card : ℚ) -
      L * ∏ i, (1 - rho i) =
      ∑ T ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℚ) ^ T.card * ((T.inf bad).card - L * ∏ i ∈ T, rho i) := by
    rw [hIE, hprod, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [heq, Finset.prod_one_add]
  calc
    _ ≤ ∑ T ∈ (Finset.univ : Finset ι).powerset,
        |(-1 : ℚ) ^ T.card * ((T.inf bad).card - L * ∏ i ∈ T, rho i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro T _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using herr T

end Erdos441

#print axioms Erdos441.sieve_discrepancy_bound
