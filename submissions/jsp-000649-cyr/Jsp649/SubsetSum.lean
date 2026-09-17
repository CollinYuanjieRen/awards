import Mathlib

namespace SubsetSumFree

def A (N : ℕ) : Finset ℕ := Finset.Icc (N / 2 + 1) N

theorem A_card (N : ℕ) : (A N).card = N - N / 2 := by
  rw [A, Nat.card_Icc]; omega

/-- No element of `A N` equals the sum of a nonempty set of distinct OTHER elements. -/
theorem A_no_subset_sum (N : ℕ) :
    ∀ a ∈ A N, ∀ T ⊆ (A N).erase a, T.Nonempty → a ≠ T.sum id := by
  intro a ha T hT hne heq
  have hxbound : ∀ x ∈ T, N / 2 + 1 ≤ x := by
    intro x hx
    have hx2 := hT hx
    rw [Finset.mem_erase] at hx2
    have hx3 := hx2.2
    rw [A, Finset.mem_Icc] at hx3
    exact hx3.1
  have ha' : a ≤ N := by rw [A, Finset.mem_Icc] at ha; exact ha.2
  rcases eq_or_lt_of_le (Finset.one_le_card.mpr hne) with h1 | h2
  · -- card = 1
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h1.symm
    subst hb
    simp only [Finset.sum_singleton, id] at heq
    have hb2 : b ∈ (A N).erase a := hT (Finset.mem_singleton_self b)
    exact (Finset.mem_erase.mp hb2).1 heq.symm
  · -- card ≥ 2
    have hsum : T.card • (N / 2 + 1) ≤ T.sum id :=
      Finset.card_nsmul_le_sum _ _ _ hxbound
    have hge2 : 2 * (N / 2 + 1) ≤ T.sum id := by
      calc 2 * (N / 2 + 1) ≤ T.card * (N / 2 + 1) := by
            exact Nat.mul_le_mul_right _ h2
        _ = T.card • (N / 2 + 1) := (smul_eq_mul _ _).symm
        _ ≤ T.sum id := hsum
    omega

theorem exists_large_subset_sum_free (N : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 N ∧ B.card = N - N / 2 ∧
      (∀ a ∈ B, ∀ T ⊆ B.erase a, T.Nonempty → a ≠ T.sum id) := by
  refine ⟨A N, ?_, A_card N, A_no_subset_sum N⟩
  rw [A]
  exact Finset.Icc_subset_Icc_left (by omega)

end SubsetSumFree

#print axioms SubsetSumFree.A_card
#print axioms SubsetSumFree.A_no_subset_sum
#print axioms SubsetSumFree.exists_large_subset_sum_free
