import MerLeanExperiment.ArcDrawing
import MerLeanExperiment.SubdivisionArcs

namespace Erdos1018Topological

open PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V} {r : ℕ}

/-- A drawn clique subdivision induces an ordinary drawing of the complete graph
on its branch vertices. -/
theorem planeDrawing_top_of_cliqueSubdivision
    (D : PlaneDrawing G) (s : Erdos1018.CliqueSubdivision G r) :
    Nonempty (PlaneDrawing (⊤ : SimpleGraph (Fin r))) := by
  apply planeDrawing_of_cliqueEdge_arcs r
    (fun i => D.point (s.branch i))
    (D.point_injective.comp s.branch.injective)
    (routeArc D s)
  · exact routeArc_isArcBetween D s
  · exact fun e i hmem => branch_point_mem_routeArc_eq_endpoint D s i e hmem
  · exact fun e f hef z hze hzf =>
      routeArc_inter_subset_branch_points D s hef hze hzf

end Erdos1018Topological
