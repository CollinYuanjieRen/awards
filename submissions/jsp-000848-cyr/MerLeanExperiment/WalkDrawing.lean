import MerLeanExperiment.DrawingAdapter
import MerLeanExperiment.Vendor.Schoenflies.Graph.CycleJordan
import MerLeanExperiment.Vendor.Schoenflies.Graph.PathGraph
import Mathlib.Combinatorics.SimpleGraph.Paths

open scoped Graph
open Schoenflies

namespace PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V}

theorem PlaneDrawing.planeGraph_isLink (D : PlaneDrawing G) {u v : V}
    (h : G.Adj u v) :
    D.planeGraph.IsLink s(u, v) (D.point u) (D.point v) := by
  exact Graph.IsLink.map D.point ⟨rfl, h⟩

theorem PlaneDrawing.planeGraph_walkVertices_edges (D : PlaneDrawing G)
    {u v : V} (p : G.Walk u v) :
    D.planeGraph.walkVertices (D.point u) p.edges =
      D.point '' {x | x ∈ p.support} := by
  induction p with
  | nil => simp [Graph.walkVertices_nil]
  | @cons u w v h p ih =>
      rw [SimpleGraph.Walk.edges_cons,
        Graph.walkVertices_cons (D.planeGraph_isLink h), ih]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_ofPred_eq,
        SimpleGraph.Walk.support_cons, List.mem_cons]
      aesop

theorem PlaneDrawing.planeGraph_isWalk (D : PlaneDrawing G)
    {u v : V} (p : G.Walk u v) :
    D.planeGraph.IsWalk (D.point u) p.edges (D.point v) := by
  induction p with
  | nil =>
      apply Graph.IsWalk.nil
      rw [D.planeGraph_vertexSet]
      exact ⟨_, rfl⟩
  | cons h p ih =>
      exact Graph.IsWalk.cons (D.planeGraph_isLink h) ih

theorem PlaneDrawing.planeGraph_isPath (D : PlaneDrawing G)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    D.planeGraph.IsPath (D.point u) p.edges (D.point v) := by
  induction p with
  | nil =>
      apply Graph.IsPath.nil
      rw [D.planeGraph_vertexSet]
      exact ⟨_, rfl⟩
  | @cons u w v h p ih =>
      have hp' : p.IsPath := by simpa using hp.tail
      refine Graph.IsPath.cons (D.planeGraph_isLink h) (ih hp') ?_
      change D.point u ∉ D.planeGraph.walkVertices (D.point w) p.edges
      rw [D.planeGraph_walkVertices_edges]
      rintro ⟨x, hx, hxu⟩
      have hux : u = x := D.point_injective hxu.symm
      subst x
      have hnodup := hp.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
      exact hnodup.1 hx

theorem PlaneDrawing.walk_isArcBetween (D : PlaneDrawing G)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (huv : u ≠ v) :
    IsArcBetween (Graph.edgesCover D.drawing p.edges) (D.point u) (D.point v) := by
  apply D.isDrawing.path_isArcBetween (D.planeGraph_isPath p hp)
  intro hedge
  have hlength : p.length = 0 := by
    rw [← p.length_edges, hedge]
    rfl
  exact huv (p.eq_of_length_eq_zero hlength)

theorem PlaneDrawing.mem_support_of_inc_edges (D : PlaneDrawing G)
    {u v x : V} (p : G.Walk u v) {e : Sym2 V}
    (he : e ∈ p.edges) (hinc : D.planeGraph.Inc e (D.point x)) :
    x ∈ p.support := by
  have hxwalk : D.point x ∈ D.planeGraph.walkVertices (D.point u) p.edges :=
    Graph.mem_walkVertices_of_mem_covered ⟨e, he, hinc⟩
  rw [D.planeGraph_walkVertices_edges] at hxwalk
  obtain ⟨y, hy, hxy⟩ := hxwalk
  exact D.point_injective hxy ▸ hy

theorem PlaneDrawing.mem_support_of_point_mem_edgesCover (D : PlaneDrawing G)
    {u v x : V} (p : G.Walk u v)
    (hx : D.point x ∈ Graph.edgesCover D.drawing p.edges) :
    x ∈ p.support := by
  obtain ⟨e, he, hxe⟩ := Graph.mem_edgesCover_iff.1 hx
  have heG : e ∈ E(D.planeGraph) := (D.planeGraph_isWalk p).edge_mem he
  obtain ⟨a, b, hab⟩ := D.planeGraph.exists_isLink_of_mem_edgeSet heG
  have hxV : D.point x ∈ V(D.planeGraph) := by
    rw [D.planeGraph_vertexSet]
    exact ⟨x, rfl⟩
  rcases D.isDrawing.vertex_mem_edgeArc hab hxV hxe with hxa | hxb
  · exact D.mem_support_of_inc_edges p he (hxa ▸ hab.inc_left)
  · exact D.mem_support_of_inc_edges p he (hxb ▸ hab.inc_right)

end PlanarListColoring
