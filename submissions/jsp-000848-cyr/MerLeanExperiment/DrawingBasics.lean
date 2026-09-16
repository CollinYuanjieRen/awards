import MerLeanExperiment.PlaneDrawing

open scoped unitInterval

namespace PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- In a simple graph the drawing is injective on the entire closed edge. -/
theorem PlaneDrawing.edge_injective (D : PlaneDrawing G) (e : G.edgeSet) :
    Function.Injective (D.edgePoint e) := by
  have hend : e.1.out.1 ≠ e.1.out.2 := by
    intro h
    apply G.not_isDiag_of_mem_edgeSet e.2
    rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
    exact h
  intro s t hst
  by_cases hs0 : s = 0
  · subst s
    by_cases ht0 : t = 0
    · exact ht0.symm
    by_cases ht1 : t = 1
    · subst t
      exfalso
      apply hend
      apply D.vertexPoint_injective
      rw [← D.edge_zero e, ← D.edge_one e]
      exact hst
    · exact (D.edge_interior_avoids_vertex e e.1.out.1 ht0 ht1
        (hst ▸ D.edge_zero e)).elim
  by_cases hs1 : s = 1
  · subst s
    by_cases ht0 : t = 0
    · subst t
      exfalso
      apply hend
      apply D.vertexPoint_injective
      rw [← D.edge_zero e, ← D.edge_one e]
      exact hst.symm
    by_cases ht1 : t = 1
    · exact ht1.symm
    · exact (D.edge_interior_avoids_vertex e e.1.out.2 ht0 ht1
        (hst ▸ D.edge_one e)).elim
  by_cases ht0 : t = 0
  · subst t
    exact (D.edge_interior_avoids_vertex e e.1.out.1 hs0 hs1
      (hst.symm ▸ D.edge_zero e)).elim
  by_cases ht1 : t = 1
  · subst t
    exact (D.edge_interior_avoids_vertex e e.1.out.2 hs0 hs1
      (hst.symm ▸ D.edge_one e)).elim
  exact D.edge_interior_injective e hs0 hs1 ht0 ht1 hst

/-- Deleting edges preserves an ordinary crossing-free drawing. -/
noncomputable def PlaneDrawing.restrict (D : PlaneDrawing G) (H : SimpleGraph V)
    (hHG : H ≤ G) : PlaneDrawing H := by
  let inc : H.edgeSet → G.edgeSet := Set.inclusion (SimpleGraph.edgeSet_mono hHG)
  exact
    { vertexPoint := D.vertexPoint
      vertexPoint_injective := D.vertexPoint_injective
      edgePoint := fun e ↦ D.edgePoint (inc e)
      edge_continuous := fun e ↦ D.edge_continuous (inc e)
      edge_zero := fun e ↦ D.edge_zero (inc e)
      edge_one := fun e ↦ D.edge_one (inc e)
      edge_interior_injective := fun e ↦ D.edge_interior_injective (inc e)
      edge_interior_avoids_vertex := fun e ↦ D.edge_interior_avoids_vertex (inc e)
      edge_interiors_disjoint := fun hef ↦ D.edge_interiors_disjoint fun h ↦
        hef (Set.inclusion_injective (SimpleGraph.edgeSet_mono hHG) h) }

end PlanarListColoring
