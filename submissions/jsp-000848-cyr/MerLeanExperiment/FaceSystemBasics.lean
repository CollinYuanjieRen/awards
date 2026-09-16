import MerLeanExperiment.FaceSystem

open scoped Graph
open Set Schoenflies

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {U : Set Plane} {W : List β}

/-- An actual enumerated face is nonempty. -/
theorem IsBoundaryList.nonempty (h : IsBoundaryList G drawing U W) : U.Nonempty := by
  obtain ⟨z, e, a, b, D, hz, rfl, hface, hperm⟩ := h
  exact ⟨z, mem_face hz⟩

/-- An actual face lies in the complement of the drawn graph. -/
theorem IsBoundaryList.subset_exterior (h : IsBoundaryList G drawing U W) :
    U ⊆ exterior G drawing := by
  obtain ⟨z, e, a, b, D, hz, rfl, hface, hperm⟩ := h
  exact face_subset_exterior G drawing z

/-- Any point in an actual face names that same connected component. -/
theorem IsBoundaryList.face_eq (h : IsBoundaryList G drawing U W)
    {z : Plane} (hz : z ∈ U) : face G drawing z = U := by
  obtain ⟨x, e, a, b, D, hx, rfl, hface, hperm⟩ := h
  exact (connectedComponentIn_eq hz).symm

/-- Distinct entries in the face enumeration have disjoint actual regions. -/
theorem FaceSystem.disjoint_regions (M : FaceSystem G drawing)
    {q r : Set Plane × List β} (hq : q ∈ M.boundaries) (hr : r ∈ M.boundaries)
    (hne : q ≠ r) : Disjoint q.1 r.1 := by
  obtain ⟨zq, eq, aq, bq, Dq, hzq, hqface, hcycleq, hpermq⟩ := M.valid q hq
  obtain ⟨zr, er, ar, br, Dr, hzr, hrface, hcycler, hpermr⟩ := M.valid r hr
  rcases face_eq_or_disjoint (G := G) (drawing := drawing) zq zr with heq | hdisj
  · exact False.elim <| hne <| M.unique (by simpa using hq) (by simpa using hr) <|
      hqface.trans (heq.trans hrface.symm)
  · rw [hqface, hrface]
    exact hdisj

/-- A finite boundary enumeration entails the existing actual-face-cycle property. -/
theorem FaceSystem.hasFaceCycles (M : FaceSystem G drawing) :
    HasFaceCycles G drawing := by
  intro z hz
  obtain ⟨q, hq, hqface⟩ := M.exhaustive z hz
  obtain ⟨x, e, a, b, D, hx, hface, hcycle, hperm⟩ := M.valid q hq
  refine ⟨e, a, b, D, hcycle.isCycle, hcycle.isSeparating, ?_⟩
  rw [← hqface, hface]
  exact hcycle.isRegionOf

end Graph
