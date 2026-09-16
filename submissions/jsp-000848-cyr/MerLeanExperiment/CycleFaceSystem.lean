import MerLeanExperiment.FaceSystemBasics

open scoped Graph Classical
open Set Schoenflies

namespace Graph

/-- The graph spanned by a drawn cycle has its two actual regions as faces,
with two copies of the same boundary edge list. -/
theorem IsDrawing.exists_cycle_faceSystem
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    {e : β} {a b : Plane} {D : List β} (hc : G.IsCycleThrough e a b D) :
    ∃ M : FaceSystem (G.cycleGraph a e D) drawing,
      M.faceCount = 2 ∧ M.boundaryLength = 2 * (e :: D).length := by
  let C := edgesCover drawing (e :: D)
  let H := G.cycleGraph a e D
  let W := e :: D
  have hsep : IsSeparating C := h.cycle_isSeparating hpoly hc
  have hcyc : H.IsCycleThrough e a b D :=
    ⟨hc.cycleGraph_isLink,
      hc.isPath.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg => by
        rw [hc.cycleGraph_edgeSet]
        exact List.mem_append_left _ hg,
      hc.notMem⟩
  obtain ⟨zi, hzi⟩ := hsep.isConnected_inside.nonempty
  obtain ⟨zo, hzo⟩ := hsep.isConnected_outside.nonempty
  have hziExt : zi ∈ exterior H drawing := by
    rw [exterior, h.pointSet_cycleGraph hc]
    exact inside_subset_compl hzi
  have hzoExt : zo ∈ exterior H drawing := by
    rw [exterior, h.pointSet_cycleGraph hc]
    exact outside_subset_compl hzo
  have hfacei : face H drawing zi = inside C := by
    rw [face, exterior, h.pointSet_cycleGraph hc]
    exact hsep.connectedComponentIn_eq_inside hzi
  have hfaceo : face H drawing zo = outside C := by
    rw [face, exterior, h.pointSet_cycleGraph hc]
    exact hsep.connectedComponentIn_eq_outside hzo
  have hboundaryi : IsBoundaryList H drawing (inside C) W := by
    refine ⟨zi, e, a, b, D, hziExt, hfacei.symm, ?_, List.Perm.refl W⟩
    exact ⟨hcyc, hsep, hfacei ▸ IsRegionOf.inside C⟩
  have hboundaryo : IsBoundaryList H drawing (outside C) W := by
    refine ⟨zo, e, a, b, D, hzoExt, hfaceo.symm, ?_, List.Perm.refl W⟩
    exact ⟨hcyc, hsep, hfaceo ▸ IsRegionOf.outside C⟩
  have hregions : inside C ≠ outside C := by
    intro heq
    exact Set.disjoint_left.mp disjoint_inside_outside hzi (heq ▸ hzi)
  let qi : Set Plane × List β := (inside C, W)
  let qo : Set Plane × List β := (outside C, W)
  have hqne : qi ≠ qo := fun heq => hregions (congrArg Prod.fst heq)
  let M : FaceSystem H drawing :=
    { boundaries := {qi, qo}
      valid := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact hboundaryi
        · exact hboundaryo
      unique := by
        intro q hq r hr hqr
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hq hr
        rcases hq with rfl | rfl <;> rcases hr with rfl | rfl
        · rfl
        · exact False.elim (hregions hqr)
        · exact False.elim (hregions hqr.symm)
        · rfl
      exhaustive := by
        intro z hz
        have hreg : IsRegionOf C (face H drawing z) := by
          rw [face, exterior, h.pointSet_cycleGraph hc]
          rw [exterior, h.pointSet_cycleGraph hc] at hz
          exact hsep.isRegionOf_connectedComponentIn hz
        rcases hreg with hreg | hreg
        · exact ⟨qi, by simp, hreg.symm⟩
        · exact ⟨qo, by simp, hreg.symm⟩ }
  refine ⟨M, ?_, ?_⟩
  · simp [M, FaceSystem.faceCount, hqne]
  · simp [M, FaceSystem.boundaryLength, hqne, qi, qo, W]
    omega

end Graph
