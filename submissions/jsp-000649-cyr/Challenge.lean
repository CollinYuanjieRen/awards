import Mathlib
/-! Mathlib-only comparator for JSP-000649 (subset-sum-free interval). NOT imported by the build. -/
namespace SubsetSumFreeChallenge

def A (N : ℕ) : Finset ℕ := Finset.Icc (N / 2 + 1) N

theorem A_card (N : ℕ) : (A N).card = N - N / 2 := by sorry

theorem A_no_subset_sum (N : ℕ) :
    ∀ a ∈ A N, ∀ T ⊆ (A N).erase a, T.Nonempty → a ≠ T.sum id := by sorry

theorem exists_large_subset_sum_free (N : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 N ∧ B.card = N - N / 2 ∧
      (∀ a ∈ B, ∀ T ⊆ B.erase a, T.Nonempty → a ≠ T.sum id) := by sorry

end SubsetSumFreeChallenge
