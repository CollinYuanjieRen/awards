import MerLeanExperiment.WeightedIncidence

namespace Erdos441

theorem weighted_two_family_incidence (A B : Finset ℕ) (J : Finset ℤ)
    (f g : ℕ → ℤ) (G : ℤ → Finset ℤ) (P Q : ℕ → ℤ → Prop)
    [∀ a j, Decidable (P a j)] [∀ b j, Decidable (Q b j)]
    (w : ℤ → ℝ) (hw : ∀ j ∈ J, 0 ≤ w j)
    (hf : Set.InjOn f (A : Set ℕ)) (hg : Set.InjOn g (B : Set ℕ))
    (hcross : ∀ a ∈ A, ∀ b ∈ B, f a ≠ g b)
    (hP : ∀ a ∈ A, ∀ j ∈ J, P a j → f a ∈ G j)
    (hQ : ∀ b ∈ B, ∀ j ∈ J, Q b j → g b ∈ G j) :
    (∑ a ∈ A, ∑ j ∈ J, if P a j then w j else 0) +
      (∑ b ∈ B, ∑ j ∈ J, if Q b j then w j else 0) ≤
        ∑ j ∈ J, ((G j).card : ℝ) * w j := by
  classical
  rw [Finset.sum_comm (s := A), Finset.sum_comm (s := B), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  let Ap := A.filter fun a => P a j
  let Bq := B.filter fun b => Q b j
  have hdis : Disjoint (Ap.image f) (Bq.image g) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hz
    obtain ⟨b, hb, hgb⟩ := Finset.mem_image.mp hz'
    exact hcross a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (hfa.trans hgb.symm)
  have hsub : Ap.image f ∪ Bq.image g ⊆ G j := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact hP a (Finset.mem_filter.mp ha).1 j hj (Finset.mem_filter.mp ha).2
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      exact hQ b (Finset.mem_filter.mp hb).1 j hj (Finset.mem_filter.mp hb).2
  have hAf : (Ap.image f).card = Ap.card :=
    Finset.card_image_of_injOn (hf.mono (Finset.filter_subset _ _))
  have hBg : (Bq.image g).card = Bq.card :=
    Finset.card_image_of_injOn (hg.mono (Finset.filter_subset _ _))
  have hcards : Ap.card + Bq.card ≤ (G j).card := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, hAf, hBg] at hh
    exact hh
  have heqA : (∑ a ∈ A, if P a j then w j else 0) = (Ap.card : ℝ) * w j := by
    rw [← Finset.sum_filter]
    simp [Ap]
  have heqB : (∑ b ∈ B, if Q b j then w j else 0) = (Bq.card : ℝ) * w j := by
    rw [← Finset.sum_filter]
    simp [Bq]
  rw [heqA, heqB, ← add_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcards) (hw j hj)

end Erdos441

#print axioms Erdos441.weighted_two_family_incidence
