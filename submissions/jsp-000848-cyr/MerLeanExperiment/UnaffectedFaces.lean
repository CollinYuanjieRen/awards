import MerLeanExperiment.FaceSystemBasics

open scoped Graph
open Set Schoenflies

namespace Graph

/-- An actual face untouched by an added graph keeps its original cycle boundary. -/
theorem IsBoundaryList.mono_union_of_disjoint
    {β : Type*} {B P : Graph Plane β} {drawing : β → ℝ → Plane}
    {U : Set Plane} {W : List β} (hU : IsBoundaryList B drawing U W)
    (hdis : Disjoint U (pointSet P drawing)) :
    IsBoundaryList (B.union P) drawing U W := by
  obtain ⟨z, e, a, b, D, hz, hUface, hface, hperm⟩ := hU
  have hdisface : Disjoint (face B drawing z) (pointSet P drawing) := by
    rw [← hUface]
    exact hdis
  have hzunion : z ∈ exterior (B.union P) drawing := by
    rw [exterior_union]
    exact ⟨hz, fun hzP => Set.disjoint_left.mp hdisface (mem_face hz) hzP⟩
  have hfaceeq : face (B.union P) drawing z = face B drawing z :=
    face_union_eq_of_disjoint hz hdisface
  exact ⟨z, e, a, b, D, hzunion, hUface.trans hfaceeq.symm,
    hface.mono (left_le_union B P) hfaceeq, hperm⟩

/-- An ear lying in one old face misses each other actual face. -/
theorem IsDrawing.ear_disjoint_of_other_face
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
    (h : IsDrawing G drawing) {a b z : Plane} {P W : List β} {U : Set Plane}
    (hpath : G.IsPath a P b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hsub : edgesCover drawing P \ {a, b} ⊆ face B drawing z)
    (hU : IsBoundaryList B drawing U W) (hdis : Disjoint U (face B drawing z)) :
    Disjoint U (pointSet (G.pathGraphOf a P) drawing) := by
  have hne : P ≠ [] := hpath.ne_nil hab
  rw [h.pointSet_pathGraphOf hpath.isWalk hne, Set.disjoint_left]
  intro w hwU hwP
  have hwext : w ∈ exterior B drawing := hU.subset_exterior hwU
  have hwends : w ∉ ({a, b} : Set Plane) := by
    rintro (rfl | rfl)
    · exact hwext (vertexSet_subset_pointSet ha)
    · exact hwext (vertexSet_subset_pointSet hb)
  exact Set.disjoint_left.mp hdis hwU (hsub ⟨hwP, hwends⟩)

end Graph
