import MerLeanExperiment.GraphSeparator
import MerLeanExperiment.Vendor.Schoenflies.Graph.Degree
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Data.Set.Card

open scoped Graph
open Set

namespace Graph

/-- A nonempty simple graph with fewer than three vertices satisfies the density bound. -/
theorem small_graph_density
    {α β : Type*} {G : Graph α β} [G.Finite] [G.Simple]
    (hne : V(G).Nonempty) (hsmall : ¬ G.HasThreeVertices) :
    E(G).ncard + 2 ≤ 2 * V(G).ncard := by
  by_cases hE : E(G) = ∅
  · rw [hE]
    simp only [Set.ncard_empty, zero_add]
    have hn : 0 < V(G).ncard :=
      (Set.ncard_pos (Graph.finite_vertexSet G)).mpr hne
    omega
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hE
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have hverts : ∀ z ∈ V(G), z = x ∨ z = y := by
    intro z hz
    by_cases hzx : z = x
    · exact Or.inl hzx
    by_cases hzy : z = y
    · exact Or.inr hzy
    exfalso
    apply hsmall
    exact ⟨x, hxy.left_mem, y, hxy.right_mem, z, hz, hxy.ne,
      fun hxz ↦ hzx hxz.symm, fun hyz ↦ hzy hyz.symm⟩
  have hedge : E(G) = {e} := by
    ext f
    constructor
    · intro hf
      obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet hf
      rcases hverts u huv.left_mem with rfl | rfl <;>
        rcases hverts v huv.right_mem with rfl | rfl
      · exact False.elim (huv.ne rfl)
      · exact Set.mem_singleton_iff.mpr (huv.eq hxy)
      · exact Set.mem_singleton_iff.mpr (huv.symm.eq hxy)
      · exact False.elim (huv.ne rfl)
    · simpa only [Set.mem_singleton_iff] using fun hfe ↦ hfe ▸ he
  have htwo : 2 ≤ V(G).ncard := by
    rw [← Set.ncard_pair hxy.ne]
    apply Set.ncard_le_ncard (ht := Graph.finite_vertexSet G)
    intro z hz
    rcases hz with rfl | rfl
    · exact hxy.left_mem
    · exact hxy.right_mem
  rw [hedge, Set.ncard_singleton]
  omega

end Graph
