import MerLeanExperiment.GraphSeparation

open scoped Graph
open Set

namespace Graph

/-- Failure of two-connectivity gives two nonempty parts separated by at most one vertex. -/
theorem exists_small_separator
    {α β : Type*} (G : Graph α β) (hthree : G.HasThreeVertices)
    (htwo : ¬ G.IsTwoConnected) :
    ∃ A B S : Set α,
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ Disjoint A S ∧ Disjoint B S ∧
      (A ∪ B) ∪ S = V(G) ∧ (S = ∅ ∨ ∃ v : α, S = {v}) ∧
      ∀ (e : β) (x y : α), G.IsLink e x y →
        (x ∈ A ∪ S ∧ y ∈ A ∪ S) ∨ (x ∈ B ∪ S ∧ y ∈ B ∪ S) := by
  by_cases hc : G.Connected
  · have hfail : ¬ ∀ ⦃v⦄, v ∈ V(G) → (G.deleteVerts {v}).Connected := by
      intro hdel
      exact htwo ⟨hthree, hc, hdel⟩
    push Not at hfail
    obtain ⟨v, hv, hvdisc⟩ := hfail
    obtain ⟨w, hw, hwv, -⟩ := hthree.exists_ne_ne v v
    have hwdel : w ∈ V(G.deleteVerts {v}) := by
      rw [vertexSet_deleteVerts]
      exact ⟨hw, by simpa using hwv⟩
    obtain ⟨A, B, hA, hB, hAB, hunion, hlink⟩ :=
      exists_partition_of_not_connected (G.deleteVerts {v}) ⟨w, hwdel⟩ hvdisc
    have hAdel : A ⊆ V(G.deleteVerts {v}) := fun x hx ↦ by
      rw [← hunion]
      exact Or.inl hx
    have hBdel : B ⊆ V(G.deleteVerts {v}) := fun x hx ↦ by
      rw [← hunion]
      exact Or.inr hx
    have hAv : Disjoint A ({v} : Set α) := Set.disjoint_left.2 fun x hxA hxv ↦ by
      have hxdel := hAdel hxA
      rw [vertexSet_deleteVerts] at hxdel
      exact hxdel.2 hxv
    have hBv : Disjoint B ({v} : Set α) := Set.disjoint_left.2 fun x hxB hxv ↦ by
      have hxdel := hBdel hxB
      rw [vertexSet_deleteVerts] at hxdel
      exact hxdel.2 hxv
    refine ⟨A, B, {v}, hA, hB, hAB, hAv, hBv, ?_, Or.inr ⟨v, rfl⟩, ?_⟩
    · rw [hunion, vertexSet_deleteVerts]
      ext x
      simp [hv]
    · intro e x y hxy
      by_cases hxv : x = v
      · by_cases hyv : y = v
        · exact Or.inl ⟨Or.inr (by simp [hxv]), Or.inr (by simp [hyv])⟩
        · have hyAB : y ∈ A ∨ y ∈ B := by
            have hyDel : y ∈ V(G.deleteVerts {v}) := by
              rw [vertexSet_deleteVerts]
              exact ⟨hxy.right_mem, by simpa using hyv⟩
            rw [← hunion] at hyDel
            exact hyDel
          rcases hyAB with hyA | hyB
          · exact Or.inl ⟨Or.inr (by simp [hxv]), Or.inl hyA⟩
          · exact Or.inr ⟨Or.inr (by simp [hxv]), Or.inl hyB⟩
      · by_cases hyv : y = v
        · have hxAB : x ∈ A ∨ x ∈ B := by
            have hxDel : x ∈ V(G.deleteVerts {v}) := by
              rw [vertexSet_deleteVerts]
              exact ⟨hxy.left_mem, by simpa using hxv⟩
            rw [← hunion] at hxDel
            exact hxDel
          rcases hxAB with hxA | hxB
          · exact Or.inl ⟨Or.inl hxA, Or.inr (by simp [hyv])⟩
          · exact Or.inr ⟨Or.inl hxB, Or.inr (by simp [hyv])⟩
        · have hxy' : (G.deleteVerts {v}).IsLink e x y :=
            (deleteVerts_isLink G {v}).2 ⟨hxy, by simpa using hxv, by simpa using hyv⟩
          rcases hlink e x y hxy' with hAA | hBB
          · exact Or.inl ⟨Or.inl hAA.1, Or.inl hAA.2⟩
          · exact Or.inr ⟨Or.inl hBB.1, Or.inl hBB.2⟩
  · obtain ⟨A, B, hA, hB, hAB, hunion, hlink⟩ :=
      exists_partition_of_not_connected G (by
        obtain ⟨p, hp, -⟩ := hthree
        exact ⟨p, hp⟩) hc
    refine ⟨A, B, ∅, hA, hB, hAB, by simp, by simp,
      by simpa using hunion, Or.inl rfl, ?_⟩
    intro e x y hxy
    rcases hlink e x y hxy with hAA | hBB
    · exact Or.inl ⟨Or.inl hAA.1, Or.inl hAA.2⟩
    · exact Or.inr ⟨Or.inl hBB.1, Or.inl hBB.2⟩

end Graph
