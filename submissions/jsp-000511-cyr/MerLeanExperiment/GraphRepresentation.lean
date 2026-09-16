import MerLeanExperiment.PlaneDrawing
import MerLeanExperiment.Vendor.Schoenflies.Graph.Drawing
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.Graph.Maps

open scoped Graph
open Schoenflies

namespace PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The same vertex point in the Euclidean normed plane. -/
noncomputable def PlaneDrawing.point (D : PlaneDrawing G) (v : V) : Plane :=
  WithLp.toLp 2 (D.vertexPoint v)

/-- Relabel the ordinary simple graph's vertices by their plane points. -/
noncomputable def PlaneDrawing.planeGraph (D : PlaneDrawing G) : Graph Plane (Sym2 V) :=
  (Graph.ofSimpleGraph G).map D.point

/-- The plane relabeling does not identify vertices. -/
theorem PlaneDrawing.point_injective (D : PlaneDrawing G) :
    Function.Injective D.point := by
  exact (WithLp.toLp_injective 2).comp D.vertexPoint_injective

/-- Relabeling keeps precisely the original edge set. -/
theorem PlaneDrawing.planeGraph_edgeSet (D : PlaneDrawing G) :
    E(D.planeGraph) = G.edgeSet := rfl

/-- All and only original vertex images are vertices of the plane graph. -/
theorem PlaneDrawing.planeGraph_vertexSet (D : PlaneDrawing G) :
    V(D.planeGraph) = Set.range D.point := by
  ext x
  simp [PlaneDrawing.planeGraph]

/-- An original simple graph remains simple after injective relabeling. -/
theorem PlaneDrawing.planeGraph_simple (D : PlaneDrawing G) : D.planeGraph.Simple := by
  refine { not_isLoopAt := ?_, eq_of_isLink := ?_ }
  · rintro e x ⟨u, v, huv, hu, hv⟩
    exact ((Graph.ofSimpleGraph_adj_iff u v).mp huv.adj).ne
      (D.point_injective (hu.trans hv.symm))
  · rintro e f x y ⟨u, v, huv, hux, hvy⟩ ⟨u', v', huv', hu'x, hv'y⟩
    have huu' : u = u' := D.point_injective (hux.trans hu'x.symm)
    have hvv' : v = v' := D.point_injective (hvy.trans hv'y.symm)
    subst u'
    subst v'
    exact huv.1.trans huv'.1.symm

/-- Both vertex and edge sets of the relabeled graph are finite. -/
theorem PlaneDrawing.planeGraph_finite [Finite V] (D : PlaneDrawing G) :
    D.planeGraph.Finite := by
  constructor
  · rw [D.planeGraph_vertexSet]
    exact Set.finite_range D.point
  · rw [D.planeGraph_edgeSet]
    exact Set.toFinite G.edgeSet

/-- The relabeling preserves the vertex count, including isolated vertices. -/
theorem PlaneDrawing.planeGraph_ncard_vertices [Fintype V] (D : PlaneDrawing G) :
    V(D.planeGraph).ncard = Fintype.card V := by
  rw [D.planeGraph_vertexSet, Set.ncard_range_of_injective D.point_injective,
    Nat.card_eq_fintype_card]

end PlanarListColoring
