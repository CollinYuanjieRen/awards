import Erdos772Sidon.Average

/-! Deleting one element per bad quadruple yields a Sidon set. -/

namespace Erdos772

theorem exists_sidon_subset (k : ℕ) (A : Finset ℕ) (hA : RepBounded k A) (s : ℕ)
    (hs : s ≤ A.card) (h6 : 6 * k * s ^ 3 ≤ A.card ^ 2) :
    ∃ S ⊆ A, IsSidon S ∧ s ≤ 2 * S.card := by
  obtain ⟨S, hS, hbad⟩ := exists_subset_few_bad k A hA s hs h6
  rw [Finset.mem_powersetCard] at hS
  obtain ⟨hSA, hScard⟩ := hS
  -- Delete the first coordinate of every bad quadruple.
  set D : Finset ℕ := (badTuples S).image (fun t => t.1.1) with hD
  refine ⟨S \ D, Finset.sdiff_subset.trans hSA, ?_, ?_⟩
  · intro a ha b hb c hc d hd heq
    by_contra hnt
    have hmem : ((a, b), (c, d)) ∈ badTuples S := by
      simp only [badTuples, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨⟨(Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp hb).1⟩,
        (Finset.mem_sdiff.mp hc).1, (Finset.mem_sdiff.mp hd).1⟩, heq, hnt⟩
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_image_of_mem (fun t => t.1.1) hmem)
  · have h1 : S.card ≤ (S \ D).card + D.card := Finset.card_le_card_sdiff_add_card
    have h2 : D.card ≤ (badTuples S).card := Finset.card_image_le
    omega

end Erdos772
