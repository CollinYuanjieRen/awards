import Jsp285.OccurrenceDyadic

/-! It suffices to balance the occupied weight classes. -/

namespace Jsp285

/-- Balance of occupied class intersections yields the full weighted mass bounds. -/
lemma dyadic_weight_balance_occupied {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y C : Finset ι) (N a b c : ℕ)
    (hY : ∀ i ∈ Y, 0 < v i ∧ v i ≤ N) (hCY : C ⊆ Y)
    (hclasses : ∀ j ∈ Finset.range (Nat.log 2 N + 1),
      (dyadicBin v Y j).Nonempty →
        a * (dyadicBin v Y j).card ≤ b * (C ∩ dyadicBin v Y j).card ∧
        b * (C ∩ dyadicBin v Y j).card ≤ c * (dyadicBin v Y j).card) :
    a * (∑ i ∈ Y, v i) ≤ 2 * b * (∑ i ∈ C, v i) ∧
      b * (∑ i ∈ C, v i) ≤ 2 * c * (∑ i ∈ Y, v i) := by
  apply dyadic_weight_balance v Y C N a b c hY hCY
  intro j hj
  have hinter : C ∩ dyadicBin v Y j = dyadicBin v C j := by
    ext i
    simp only [Finset.mem_inter, dyadicBin, Finset.mem_filter]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hCY h.1, h.2⟩⟩
  by_cases hne : (dyadicBin v Y j).Nonempty
  · simpa [hinter] using hclasses j hj hne
  · have he : dyadicBin v Y j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hC : dyadicBin v C j = ∅ := by rw [← hinter, he]; simp
    simp [he, hC]

end Jsp285
