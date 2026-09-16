import MerLeanExperiment.PlanarTriangularBound
import MerLeanExperiment.DrawingAdapter
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Sym.NatCard

open scoped Graph
open Schoenflies

namespace Erdos1018Topological

open PlanarListColoring

/-- The relabeled complete graph has a named edge between every two distinct vertices. -/
private theorem complete_planeGraph_isLink
    (D : PlaneDrawing (⊤ : SimpleGraph (Fin 5))) {i j : Fin 5} (hij : i ≠ j) :
    D.planeGraph.IsLink s(i, j) (D.point i) (D.point j) := by
  apply Graph.IsLink.map D.point
  exact ⟨rfl, hij⟩

/-- The drawing graph of the complete graph on five vertices is two-connected. -/
private theorem complete_planeGraph_isTwoConnected
    (D : PlaneDrawing (⊤ : SimpleGraph (Fin 5))) : D.planeGraph.IsTwoConnected := by
  have hmem (i : Fin 5) : D.point i ∈ V(D.planeGraph) := by
    rw [D.planeGraph_vertexSet]
    exact ⟨i, rfl⟩
  have hreaches {i j : Fin 5} : D.planeGraph.Reaches (D.point i) (D.point j) := by
    by_cases hij : i = j
    · subst j
      exact Graph.Reaches.refl (hmem i)
    · exact Graph.Reaches.of_isLink (complete_planeGraph_isLink D hij)
  refine { hasThreeVertices := ?_, connected := ?_, deleteVerts_connected := ?_ }
  · refine ⟨D.point 0, hmem 0, D.point 1, hmem 1, D.point 2, hmem 2, ?_, ?_, ?_⟩
    · show D.point (0 : Fin 5) ≠ D.point 1
      exact D.point_injective.ne (by decide)
    · show D.point (0 : Fin 5) ≠ D.point 2
      exact D.point_injective.ne (by decide)
    · show D.point (1 : Fin 5) ≠ D.point 2
      exact D.point_injective.ne (by decide)
  · refine Graph.Connected.of_hub (hmem 0) ?_
    intro p hp
    rw [D.planeGraph_vertexSet] at hp
    obtain ⟨i, rfl⟩ := hp
    exact hreaches
  · intro x hx
    rw [D.planeGraph_vertexSet] at hx
    obtain ⟨k, rfl⟩ := hx
    let i : Fin 5 := if k = 0 then 1 else 0
    have hik : i ≠ k := by
      dsimp [i]
      split
      · next h => subst k; decide
      · next h => exact Ne.symm h
    have hi : D.point i ∈ V(D.planeGraph.deleteVerts {D.point k}) :=
      Graph.mem_deleteVerts_singleton_of_ne (hmem i) (D.point_injective.ne hik)
    refine Graph.Connected.of_hub hi ?_
    intro p hp
    rw [Graph.mem_deleteVerts_singleton] at hp
    rw [D.planeGraph_vertexSet] at hp
    obtain ⟨⟨j, rfl⟩, hjk⟩ := hp
    by_cases hij : i = j
    · subst j
      exact Graph.Reaches.refl hi
    · apply Graph.Reaches.of_isLink
      rw [Graph.deleteVerts_isLink]
      exact ⟨complete_planeGraph_isLink D hij,
        D.point_injective.ne hik, hjk⟩

/-- The complete graph on five vertices has no crossing-free plane drawing. -/
theorem completeFive_no_drawing :
    ¬ Nonempty (PlaneDrawing (⊤ : SimpleGraph (Fin 5))) := by
  rintro ⟨D⟩
  have hfinite : D.planeGraph.Finite := D.planeGraph_finite
  have hsimple : D.planeGraph.Simple := D.planeGraph_simple
  have hbound := D.isDrawing.twoConnected_triangular_density
    (complete_planeGraph_isTwoConnected D)
  have hvert : V(D.planeGraph).ncard = 5 := by
    simpa using D.planeGraph_ncard_vertices
  have hedge : E(D.planeGraph).ncard = 10 := by
    rw [D.planeGraph_edgeSet]
    rw [SimpleGraph.edgeSet_top, Sym2.ncard_diagSet_compl]
    rw [Nat.card_fin]
    decide
  omega

end Erdos1018Topological
