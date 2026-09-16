import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos441

theorem weighted_incidence_le_cards {ι κ α : Type*} [DecidableEq α]
    (S : Finset ι) (J : Finset κ) (F : ι → α) (hF : Function.Injective F)
    (A : κ → Finset α) (w : κ → ℝ) (hw : ∀ j ∈ J, 0 ≤ w j) :
    (∑ i ∈ S, ∑ j ∈ J, if F i ∈ A j then w j else 0) ≤
      ∑ j ∈ J, ((A j).card : ℝ) * w j := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  have hcard : (S.filter fun i => F i ∈ A j).card ≤ (A j).card := by
    apply Finset.card_le_card_of_injOn F
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact hF.injOn
  calc
    _ = ((S.filter fun i => F i ∈ A j).card : ℝ) * w j := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (hw j hj)

end Erdos441

#print axioms Erdos441.weighted_incidence_le_cards
