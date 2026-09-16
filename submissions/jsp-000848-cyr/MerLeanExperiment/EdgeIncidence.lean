import MerLeanExperiment.EdgeParameters

open scoped unitInterval
open Schoenflies

namespace PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A vertex met by a drawn edge is one of its endpoints. -/
theorem PlaneDrawing.edgeParam_eq_point (D : PlaneDrawing G) (e : G.edgeSet)
    (t : I) (v : V) (h : D.edgeParam e (t : ℝ) = D.point v) :
    v = e.1.out.1 ∨ v = e.1.out.2 := by
  have hraw : D.edgePoint e t = D.vertexPoint v := by
    apply WithLp.toLp_injective 2
    simpa [PlaneDrawing.point, D.edgeParam_coe e t] using h
  by_cases ht0 : t = 0
  · left
    apply D.vertexPoint_injective
    subst t
    exact hraw.symm.trans (D.edge_zero e)
  by_cases ht1 : t = 1
  · right
    apply D.vertexPoint_injective
    subst t
    exact hraw.symm.trans (D.edge_one e)
  exact (D.edge_interior_avoids_vertex e v ht0 ht1 hraw).elim

/-- Distinct edge arcs intersect only at an original vertex image. -/
theorem PlaneDrawing.edgeParam_inter_vertex (D : PlaneDrawing G) (e f : G.edgeSet)
    (hef : e ≠ f) (s t : I)
    (h : D.edgeParam e (s : ℝ) = D.edgeParam f (t : ℝ)) :
    ∃ v : V, D.edgeParam e (s : ℝ) = D.point v := by
  by_cases hs0 : s = 0
  · exact ⟨e.1.out.1, hs0 ▸ D.edgeParam_zero e⟩
  by_cases hs1 : s = 1
  · exact ⟨e.1.out.2, hs1 ▸ D.edgeParam_one e⟩
  by_cases ht0 : t = 0
  · exact ⟨f.1.out.1, h.trans (ht0 ▸ D.edgeParam_zero f)⟩
  by_cases ht1 : t = 1
  · exact ⟨f.1.out.2, h.trans (ht1 ▸ D.edgeParam_one f)⟩
  exfalso
  apply D.edge_interiors_disjoint hef hs0 hs1 ht0 ht1
  apply WithLp.toLp_injective 2
  simpa [D.edgeParam_coe e s, D.edgeParam_coe f t] using h

end PlanarListColoring
