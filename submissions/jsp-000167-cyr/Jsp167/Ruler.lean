import Mathlib

namespace SparseRuler

/-- `S` measures every length in `{1,…,L}`: each such `k` is a difference of two marks. -/
def Measures (S : Finset ℕ) (L : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 L, ∃ a ∈ S, ∃ b ∈ S, b < a ∧ a - b = k

/-- Counting lower bound: a ruler measuring `{1,…,L}` needs `C(|S|,2) ≥ L`. -/
theorem card_choose_two_ge {S : Finset ℕ} {L : ℕ} (h : Measures S L) :
    L ≤ S.card.choose 2 := by
  classical
  set P : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun p => p.2 < p.1) with hP
  set D : Finset ℕ := P.image (fun p => p.1 - p.2) with hD
  -- Step 1: Icc 1 L ⊆ D
  have step1 : Finset.Icc 1 L ⊆ D := by
    intro k hk
    obtain ⟨a, ha, b, hb, hlt, hdiff⟩ := h k hk
    apply Finset.mem_image.mpr
    refine ⟨(a, b), ?_, hdiff⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hlt⟩
  -- Step 2: L ≤ D.card
  have hcardIcc : (Finset.Icc 1 L).card = L := by
    rw [Nat.card_Icc]; omega
  have step2 : L ≤ D.card := by
    have := Finset.card_le_card step1
    rw [hcardIcc] at this
    exact this
  -- Step 3: D.card ≤ P.card
  have step3 : D.card ≤ P.card := Finset.card_image_le
  -- Step 4: P.card ≤ S.card.choose 2 via injection into powersetCard 2
  have step4 : P.card ≤ S.card.choose 2 := by
    have hmaps : ∀ p ∈ P, ({p.1, p.2} : Finset ℕ) ∈ S.powersetCard 2 := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hlt⟩ := hp
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hp1
        · exact hp2
      · have hne : p.1 ≠ p.2 := by omega
        exact Finset.card_pair hne
    have hinj : ∀ p ∈ P, ∀ q ∈ P,
        ({p.1, p.2} : Finset ℕ) = {q.1, q.2} → p = q := by
      intro p hp q hq heq
      rw [hP, Finset.mem_filter] at hp hq
      have hplt : p.2 < p.1 := hp.2
      have hqlt : q.2 < q.1 := hq.2
      -- p.1 ∈ {q.1, q.2}, p.2 ∈ {q.1, q.2}, and symmetric
      have hp1 : p.1 ∈ ({q.1, q.2} : Finset ℕ) := by
        rw [← heq]; simp
      have hp2 : p.2 ∈ ({q.1, q.2} : Finset ℕ) := by
        rw [← heq]; simp
      have hq1 : q.1 ∈ ({p.1, p.2} : Finset ℕ) := by
        rw [heq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2 hq1
      have : p.1 = q.1 ∧ p.2 = q.2 := by omega
      exact Prod.ext this.1 this.2
    have := Finset.card_le_card_of_injOn (f := fun p => ({p.1, p.2} : Finset ℕ))
      (fun p hp => Finset.mem_coe.mpr (hmaps p (Finset.mem_coe.mp hp)))
      (fun p hp q hq => hinj p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq))
    rwa [Finset.card_powersetCard] at this
  calc L ≤ D.card := step2
    _ ≤ P.card := step3
    _ ≤ S.card.choose 2 := step4

/-- The 4-mark ruler {0,1,4,6} measures every length 1..6 (a perfect ruler). -/
theorem perfect_ruler_0146 : Measures ({0, 1, 4, 6} : Finset ℕ) 6 := by
  intro k hk
  fin_cases hk <;> decide

#print axioms SparseRuler.card_choose_two_ge
#print axioms SparseRuler.perfect_ruler_0146

end SparseRuler
