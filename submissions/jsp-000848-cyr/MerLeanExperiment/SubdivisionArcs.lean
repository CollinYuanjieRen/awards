import MerLeanExperiment.WalkDrawing
import MerLeanExperiment.SubdivisionRoutes

open scoped Graph
open Schoenflies

namespace PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V} {r : ℕ}

/-- The drawn point set of one route in a clique subdivision. -/
def routeArc (D : PlaneDrawing G) (s : Erdos1018.CliqueSubdivision G r)
    (e : Erdos1018.CliqueEdge r) : Set Plane :=
  Graph.edgesCover D.drawing (s.path e).edges

theorem routeArc_isArcBetween (D : PlaneDrawing G)
    (s : Erdos1018.CliqueSubdivision G r) (e : Erdos1018.CliqueEdge r) :
    IsArcBetween (routeArc D s e) (D.point (s.branch e.1.1))
      (D.point (s.branch e.1.2)) := by
  apply D.walk_isArcBetween (s.path e) (s.path_isPath e)
  exact s.branch.injective.ne (ne_of_lt e.2)

theorem branch_point_mem_routeArc_eq_endpoint (D : PlaneDrawing G)
    (s : Erdos1018.CliqueSubdivision G r) (i : Fin r)
    (e : Erdos1018.CliqueEdge r)
    (hmem : D.point (s.branch i) ∈ routeArc D s e) :
    i = e.1.1 ∨ i = e.1.2 := by
  apply s.branch_mem_support_eq_endpoint i e
  exact D.mem_support_of_point_mem_edgesCover (s.path e) hmem

theorem routeArc_inter_subset_branch_points (D : PlaneDrawing G)
    (s : Erdos1018.CliqueSubdivision G r) {e f : Erdos1018.CliqueEdge r}
    (hef : e ≠ f) {z : Plane} (hze : z ∈ routeArc D s e)
    (hzf : z ∈ routeArc D s f) :
    z ∈ Set.range (fun i => D.point (s.branch i)) := by
  obtain ⟨g, hge, hzg⟩ := Graph.mem_edgesCover_iff.1 hze
  obtain ⟨h, hhf, hzh⟩ := Graph.mem_edgesCover_iff.1 hzf
  have hgh : g ≠ h := by
    intro hEq
    subst h
    exact s.path_edges_disjoint hef hge hhf
  have hwE := D.planeGraph_isWalk (s.path e)
  have hwF := D.planeGraph_isWalk (s.path f)
  obtain ⟨hzV, hzgInc, hzhInc⟩ :=
    D.isDrawing.edge_inter (hwE.edge_mem hge) (hwF.edge_mem hhf) hgh hzg hzh
  rw [D.planeGraph_vertexSet] at hzV
  obtain ⟨x, rfl⟩ := hzV
  have hxe : x ∈ (s.path e).support :=
    D.mem_support_of_inc_edges (s.path e) hge hzgInc
  have hxf : x ∈ (s.path f).support :=
    D.mem_support_of_inc_edges (s.path f) hhf hzhInc
  rcases (s.support_inter_eq_endpoints hef hxe hxf).1 with hx | hx
  · exact ⟨e.1.1, congrArg D.point hx.symm⟩
  · exact ⟨e.1.2, congrArg D.point hx.symm⟩

end PlanarListColoring
