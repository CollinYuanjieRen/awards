import Mathlib
import Proof.Defs
import Proof.Model

/-!
# Transfer to `Fin N`

Embedding the vertex type `Vtx n` into `Fin N` (for `N ≥ |Vtx n|`) and mapping the graph along
the embedding gives a graph on `Fin N` with the same number of edges whose extra vertices are
isolated.  A `D`-balanced subgraph `H` of the mapped graph is therefore either edgeless (as soon
as it uses one of the extra, isolated vertices), or it lives inside the image of the embedding and
pulls back to a `D`-balanced subgraph `H'` of the original graph with the same numbers of vertices
and edges.
-/

open SimpleGraph

namespace Erdos803

variable {V W : Type*} {G : SimpleGraph V} {e : V ↪ W} {H : (G.map e).Subgraph}

/-- The pullback of a subgraph of `G.map e` along the embedding `e`. -/
private def pullback (e : V ↪ W) (H : (G.map e).Subgraph) : G.Subgraph where
  verts := e ⁻¹' H.verts
  Adj u v := H.Adj (e u) (e v)
  adj_sub {u v} h := by
    obtain ⟨u', v', hadj, hu, hv⟩ := (SimpleGraph.map_adj e G _ _).mp (H.adj_sub h)
    rwa [e.injective hu, e.injective hv] at hadj
  edge_vert {_ _} h := H.edge_vert h
  symm.symm _ _ h := H.adj_symm h

/-- The `pullback` neighbourhoods are the preimages of the original ones. -/
private theorem pullback_neighborSet (u : V) :
    (pullback e H).neighborSet u = e ⁻¹' H.neighborSet (e u) := rfl

/-- If `H` only uses vertices in the range of `e`, its edge set is the image of the edge set of
the pullback. -/
private theorem pullback_edgeSet (hsub : H.verts ⊆ Set.range e) :
    H.edgeSet = e.sym2Map '' (pullback e H).edgeSet := by
  refine Set.Subset.antisymm (fun s hs ↦ ?_) ?_
  · induction s using Sym2.ind with
    | _ a b =>
      rw [Subgraph.mem_edgeSet] at hs
      obtain ⟨u, rfl⟩ := hsub (H.edge_vert hs)
      obtain ⟨v, rfl⟩ := hsub (H.edge_vert (H.adj_symm hs))
      exact ⟨s(u, v), hs, rfl⟩
  · rintro s ⟨t, ht, rfl⟩
    induction t using Sym2.ind with
    | _ u v => exact ht

/-- If `H` only uses vertices in the range of `e`, degrees are preserved by the pullback. -/
private theorem sdeg_pullback (hsub : H.verts ⊆ Set.range e) (u : V) :
    sdeg (pullback e H) u = sdeg H (e u) := by
  rw [sdeg, sdeg, pullback_neighborSet, Set.ncard_preimage_of_injective_subset_range e.injective
    ((H.neighborSet_subset_verts _).trans hsub)]

/-- A vertex outside the range of `e` is isolated in `G.map e`, hence in every subgraph. -/
private theorem sdeg_eq_zero_of_notMem_range {w : W} (hw : w ∉ Set.range e) : sdeg H w = 0 := by
  have hempty : H.neighborSet w = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨u', _, _, hu', _⟩ := (SimpleGraph.map_adj e G _ _).mp (H.adj_sub hx)
    exact hw ⟨u', hu'⟩
  rw [sdeg, hempty, Set.ncard_empty]

/-- Mapping `graphOf f` along an embedding of `Vtx n` into `Fin N` gives a graph on `Fin N` with
the same number of edges, each of whose `D`-balanced subgraphs is either edgeless or comes from a
`D`-balanced subgraph of `graphOf f` with the same numbers of vertices and edges. -/
theorem exists_graph_fin (n N : ℕ) (hN : Fintype.card (Vtx n) ≤ N) (f : Choice n) :
    ∃ G : SimpleGraph (Fin N), G.edgeSet.ncard = (graphOf f).edgeSet.ncard ∧
      ∀ H : G.Subgraph, ∀ D : ℝ, Balanced D H → H.edgeSet = ∅ ∨
        ∃ H' : (graphOf f).Subgraph, H'.edgeSet.ncard = H.edgeSet.ncard ∧
          H'.verts.ncard = H.verts.ncard ∧ Balanced D H' := by
  classical
  obtain ⟨e⟩ : Nonempty (Vtx n ↪ Fin N) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hN)
  refine ⟨(graphOf f).map e, ?_, fun H D hD ↦ ?_⟩
  · rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ e.sym2Map.injective]
  by_cases hsub : H.verts ⊆ Set.range e
  · refine Or.inr ⟨pullback e H, ?_, ?_, ?_⟩
    · rw [pullback_edgeSet hsub, Set.ncard_image_of_injective _ e.sym2Map.injective]
    · exact Set.ncard_preimage_of_injective_subset_range e.injective hsub
    · intro u hu v hv
      rw [sdeg_pullback hsub, sdeg_pullback hsub]
      exact hD _ hu _ hv
  · obtain ⟨w, hw, hwr⟩ := Set.not_subset.mp hsub
    exact Or.inl (hD.edgeSet_eq_empty_of_sdeg_eq_zero hw (sdeg_eq_zero_of_notMem_range hwr))

end Erdos803
