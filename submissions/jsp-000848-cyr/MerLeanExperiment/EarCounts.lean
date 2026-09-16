import MerLeanExperiment.PathCounts
import MerLeanExperiment.Vendor.Schoenflies.FaceCycles

open scoped Graph
open Set

namespace Graph

variable {α β : Type*} {G B : Graph α β} [G.Finite]
    {a b : α} {P : List β}

/-- A proper ear adds exactly its path length many new edges. -/
theorem ncard_edges_union_ear (hBG : B ≤ G) (hpath : G.IsPath a P b)
    (hnew : ∀ e ∈ P, e ∉ E(B)) :
    E(B.union (G.pathGraphOf a P)).ncard = E(B).ncard + P.length := by
  let _ : B.Finite := Graph.Finite.of_le hBG
  have hdisj : Disjoint E(B) {e | e ∈ P} :=
    Set.disjoint_left.2 fun _ heB heP ↦ hnew _ heP heB
  have hPfinite : {e | e ∈ P}.Finite := List.finite_toSet P
  rw [edgeSet_union_pathGraphOf hpath.isWalk,
    Set.ncard_union_eq hdisj (Graph.finite_edgeSet B) hPfinite]
  have hcount : {e | e ∈ P}.ncard = P.length := by
    rw [← pathGraphOf_edgeSet hpath.isWalk]
    exact hpath.ncard_pathGraphOf_edges
  rw [hcount]

/-- An ear with two old endpoints adds all its internal vertices and no others. -/
theorem ncard_vertices_union_ear (hBG : B ≤ G) (hpath : G.IsPath a P b)
    (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B)) :
    V(B.union (G.pathGraphOf a P)).ncard + 1 = V(B).ncard + P.length := by
  let _ : B.Finite := Graph.Finite.of_le hBG
  have hinter : V(B) ∩ G.walkVertices a P = {a, b} := by
    ext y
    constructor
    · rintro ⟨hyB, hyP⟩
      by_cases hya : y = a
      · simp [hya]
      by_cases hyb : y = b
      · simp [hyb]
      exact (hint y hyP hya hyb hyB).elim
    · intro hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨ha, mem_walkVertices_self⟩
      · exact ⟨hb, hpath.target_mem_walkVertices⟩
  have hcard := Set.ncard_union_add_ncard_inter (V(B)) (G.walkVertices a P)
    (Graph.finite_vertexSet B) hpath.isWalk.finite_walkVertices
  rw [hinter, Set.ncard_pair hab, hpath.ncard_walkVertices] at hcard
  rw [vertexSet_union_pathGraphOf]
  omega

end Graph
