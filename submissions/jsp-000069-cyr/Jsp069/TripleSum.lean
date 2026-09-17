import Mathlib

namespace Erdos41

/-- `A` has distinct triple sums: distinct 3-element subsets of `A` have distinct sums. -/
def DistinctTripleSums (A : Finset ℕ) : Prop :=
  ∀ s ∈ A.powersetCard 3, ∀ t ∈ A.powersetCard 3, (s.sum id) = (t.sum id) → s = t

/-- Elementary N^{1/3} upper bound: a distinct-triple-sum set in {1..N} has at most 3N triples. -/
theorem choose_three_le {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hD : DistinctTripleSums A) :
    A.card.choose 3 ≤ 3 * N := by
  rw [← Finset.card_powersetCard]
  have hIcc : (Finset.Icc 1 (3 * N)).card = 3 * N := by
    rw [Nat.card_Icc]; omega
  rw [← hIcc]
  apply Finset.card_le_card_of_injOn (f := fun s => s.sum id)
  · -- maps into Icc 1 (3*N)
    intro s hs
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    obtain ⟨hsub, hcard⟩ := hs
    rw [Finset.mem_coe, Finset.mem_Icc]
    dsimp only
    constructor
    · -- lower bound: 1 ≤ s.sum id
      have hlow : s.card • 1 ≤ s.sum id := by
        apply Finset.card_nsmul_le_sum
        intro x hx
        have : x ∈ Finset.Icc 1 N := hA (hsub hx)
        rw [Finset.mem_Icc] at this
        exact this.1
      rw [hcard, smul_eq_mul] at hlow
      omega
    · -- upper bound: s.sum id ≤ 3*N
      have hup : s.sum id ≤ s.card • N := by
        apply Finset.sum_le_card_nsmul
        intro x hx
        have : x ∈ Finset.Icc 1 N := hA (hsub hx)
        rw [Finset.mem_Icc] at this
        exact this.2
      rw [hcard, smul_eq_mul] at hup
      exact hup
  · -- injective on the powersetCard set
    intro s hs t ht hst
    rw [Finset.mem_coe] at hs ht
    exact hD s hs t ht hst

#print axioms Erdos41.choose_three_le

end Erdos41
