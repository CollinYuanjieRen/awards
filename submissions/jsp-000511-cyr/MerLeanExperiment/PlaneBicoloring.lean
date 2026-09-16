import MerLeanExperiment.GraphRepresentation
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open scoped Graph
open Schoenflies

namespace PlanarListColoring

/-- An original bipartition extends to the relabeled plane graph. -/
theorem PlaneDrawing.exists_bicoloring
    {V : Type*} {G : SimpleGraph V} (D : PlaneDrawing G) (hbipartite : G.IsBipartite) :
    ∃ c : Plane → Fin 2,
      ∀ (e : Sym2 V) (x y : Plane), D.planeGraph.IsLink e x y → c x ≠ c y := by
  obtain ⟨C⟩ := hbipartite
  let c : Plane → Fin 2 := Function.extend D.point C fun _ => 0
  refine ⟨c, ?_⟩
  rintro e x y ⟨u, v, hlink, rfl, rfl⟩
  have hadj : G.Adj u v := (Graph.ofSimpleGraph_adj_iff u v).mp hlink.adj
  have hcu : c (D.point u) = C u := D.point_injective.extend_apply C (fun _ => 0) u
  have hcv : c (D.point v) = C v := D.point_injective.extend_apply C (fun _ => 0) v
  rw [hcu, hcv]
  exact C.valid hadj

end PlanarListColoring
