import MerLeanExperiment.GraphRepresentation
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Data.Set.Card

open scoped Graph
open Schoenflies

namespace PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V}
noncomputable local instance decidableEqForEdgeSupportedGraph : DecidableEq V := Classical.decEq V

/-- A finite edge family is realized with exactly its incident vertices. -/
theorem PlaneDrawing.exists_edgeSupported_subgraph
    (D : PlaneDrawing G) (F : Finset G.edgeSet) :
    ∃ H : Graph Plane (Sym2 V), H ≤ D.planeGraph ∧
      E(H).ncard = F.card ∧ V(H).ncard = (F.biUnion fun e => e.1.toFinset).card := by
  let names : Set (Sym2 V) := Subtype.val '' (↑F : Set G.edgeSet)
  let endpoints : Finset V := F.biUnion fun e => e.1.toFinset
  let X : Set Plane := D.point '' (↑endpoints : Set V)
  let H : Graph Plane (Sym2 V) := (D.planeGraph.restrict names).induce X
  have hX : X ⊆ V(D.planeGraph.restrict names) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    change D.point v ∈ V(D.planeGraph)
    rw [D.planeGraph_vertexSet]
    exact ⟨v, rfl⟩
  have hHG : H ≤ D.planeGraph :=
    (Graph.induce_le hX).trans Graph.restrict_le
  have hedges : E(H) = names := by
    ext edge
    constructor
    · intro hedge
      rw [Graph.edgeSet_induce] at hedge
      obtain ⟨x, y, hlink, hx, hy⟩ := hedge
      exact hlink.1
    · rintro ⟨edge', hedge'F, rfl⟩
      have hlink₀ : (Graph.ofSimpleGraph G).IsLink edge'.1 edge'.1.out.1 edge'.1.out.2 :=
        ⟨edge'.1.out_eq.symm, edge'.2⟩
      have hlink : (D.planeGraph.restrict names).IsLink edge'.1
          (D.point edge'.1.out.1) (D.point edge'.1.out.2) :=
        ⟨⟨edge', hedge'F, rfl⟩, hlink₀.map D.point⟩
      have hleft : D.point edge'.1.out.1 ∈ X := by
        refine ⟨edge'.1.out.1, ?_, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨edge', hedge'F,
          Sym2.mem_toFinset.mpr (Sym2.out_fst_mem edge'.1)⟩
      have hright : D.point edge'.1.out.2 ∈ X := by
        refine ⟨edge'.1.out.2, ?_, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨edge', hedge'F,
          Sym2.mem_toFinset.mpr (Sym2.out_snd_mem edge'.1)⟩
      rw [Graph.edgeSet_induce]
      exact ⟨D.point edge'.1.out.1, D.point edge'.1.out.2,
        hlink, hleft, hright⟩
  refine ⟨H, hHG, ?_, ?_⟩
  · rw [hedges, Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.ncard_coe_finset]
  · change X.ncard = endpoints.card
    rw [Set.ncard_image_of_injective _ D.point_injective, Set.ncard_coe_finset]

end PlanarListColoring
