import MerLeanExperiment.GraphSeparator
import MerLeanExperiment.Vendor.Schoenflies.Graph.Degree
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Data.Set.Card

open scoped Graph
open Set

namespace Graph

/-- The two induced halves of a separator partition the edges and have smaller vertex sets. -/
theorem small_separator_counts
    {α β : Type*} {G : Graph α β} [G.Finite] [G.Simple]
    {A B S : Set α} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hcover : (A ∪ B) ∪ S = V(G)) (hS : S = ∅ ∨ ∃ v : α, S = {v})
    (hlink : ∀ (e : β) (x y : α), G.IsLink e x y →
      (x ∈ A ∪ S ∧ y ∈ A ∪ S) ∨ (x ∈ B ∪ S ∧ y ∈ B ∪ S)) :
    G.induce (A ∪ S) ≤ G ∧ G.induce (B ∪ S) ≤ G ∧
    (A ∪ S).Nonempty ∧ (B ∪ S).Nonempty ∧
    (A ∪ S).ncard < V(G).ncard ∧ (B ∪ S).ncard < V(G).ncard ∧
    (A ∪ S).ncard + (B ∪ S).ncard ≤ V(G).ncard + 1 ∧
    E(G.induce (A ∪ S)).ncard + E(G.induce (B ∪ S)).ncard = E(G).ncard := by
  let X := A ∪ S
  let Y := B ∪ S
  have hXsub : X ⊆ V(G) := by
    intro x hx
    rw [← hcover]
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  have hYsub : Y ⊆ V(G) := by
    intro x hx
    rw [← hcover]
    rcases hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  have hGX : G.induce X ≤ G := G.induce_le hXsub
  have hGY : G.induce Y ≤ G := G.induce_le hYsub
  have hXne : X.Nonempty := hA.mono Set.subset_union_left
  have hYne : Y.Nonempty := hB.mono Set.subset_union_left
  have hXlt : X.ncard < V(G).ncard := by
    apply Set.ncard_lt_ncard (ht := Graph.finite_vertexSet G)
    refine ⟨hXsub, ?_⟩
    obtain ⟨b, hb⟩ := hB
    intro hsub
    rcases hsub (hYsub (Or.inl hb)) with hbA | hbS
    · exact Set.disjoint_left.1 hAB hbA hb
    · exact Set.disjoint_left.1 hBS hb hbS
  have hYlt : Y.ncard < V(G).ncard := by
    apply Set.ncard_lt_ncard (ht := Graph.finite_vertexSet G)
    refine ⟨hYsub, ?_⟩
    obtain ⟨a, ha⟩ := hA
    intro hsub
    rcases hsub (hXsub (Or.inl ha)) with haB | haS
    · exact Set.disjoint_left.1 hAB ha haB
    · exact Set.disjoint_left.1 hAS ha haS
  have hXYunion : X ∪ Y = V(G) := by
    rw [← hcover]
    ext x
    constructor
    · rintro ((hxA | hxS) | hxB | hxS)
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr hxS
      · exact Or.inl (Or.inr hxB)
      · exact Or.inr hxS
    · rintro ((hxA | hxB) | hxS)
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr (Or.inl hxB)
      · exact Or.inl (Or.inr hxS)
  have hXYinter : X ∩ Y = S := by
    ext x
    constructor
    · rintro ⟨hxA | hxS, hxB | hxS'⟩
      · exact False.elim (Set.disjoint_left.1 hAB hxA hxB)
      · exact hxS'
      · exact hxS
      · exact hxS
    · exact fun hx ↦ ⟨Or.inr hx, Or.inr hx⟩
  have hScard : S.ncard ≤ 1 := by
    rcases hS with rfl | ⟨v, rfl⟩ <;> simp
  have hvertices : X.ncard + Y.ncard ≤ V(G).ncard + 1 := by
    have hcard := Set.ncard_union_add_ncard_inter X Y
      ((Graph.finite_vertexSet G).subset hXsub)
      ((Graph.finite_vertexSet G).subset hYsub)
    rw [hXYunion, hXYinter] at hcard
    omega
  have hedgeUnion : E(G.induce X) ∪ E(G.induce Y) = E(G) := by
    ext e
    constructor
    · rintro (he | he)
      · obtain ⟨x, y, hxy, -⟩ := (G.edgeSet_induce X ▸ he)
        exact hxy.edge_mem
      · obtain ⟨x, y, hxy, -⟩ := (G.edgeSet_induce Y ▸ he)
        exact hxy.edge_mem
    · intro he
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      rcases hlink e x y hxy with hX | hY
      · exact Or.inl (G.edgeSet_induce X ▸ ⟨x, y, hxy, hX⟩)
      · exact Or.inr (G.edgeSet_induce Y ▸ ⟨x, y, hxy, hY⟩)
  have hedgeDisjoint : Disjoint E(G.induce X) E(G.induce Y) := by
    rw [Set.disjoint_left]
    intro e heX heY
    obtain ⟨x, y, hxy, hxX, hyX⟩ := G.edgeSet_induce X ▸ heX
    obtain ⟨u, v, huv, huY, hvY⟩ := G.edgeSet_induce Y ▸ heY
    have hxY : x ∈ Y := (hxy.left_eq_or_eq huv).elim (· ▸ huY) (· ▸ hvY)
    have hyY : y ∈ Y := (hxy.right_eq_or_eq huv).elim (· ▸ huY) (· ▸ hvY)
    have hxS : x ∈ S := hXYinter ▸ ⟨hxX, hxY⟩
    have hyS : y ∈ S := hXYinter ▸ ⟨hyX, hyY⟩
    rcases hS with rfl | ⟨s, rfl⟩
    · exact hxS.elim
    · exact hxy.ne (Set.mem_singleton_iff.1 hxS |>.trans
        (Set.mem_singleton_iff.1 hyS).symm)
  let _ : (G.induce X).Finite := Graph.Finite.of_le hGX
  let _ : (G.induce Y).Finite := Graph.Finite.of_le hGY
  have hedges := Set.ncard_union_eq hedgeDisjoint
    (Graph.finite_edgeSet (G.induce X)) (Graph.finite_edgeSet (G.induce Y))
  rw [hedgeUnion] at hedges
  exact ⟨hGX, hGY, hXne, hYne, hXlt, hYlt, hvertices, hedges.symm⟩

end Graph
