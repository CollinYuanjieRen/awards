import MerLeanExperiment.EarFaceSplit
import MerLeanExperiment.UnaffectedFaces
import MerLeanExperiment.FaceReplacement

open scoped Graph
open Set Schoenflies

namespace Graph

/-- Adding a proper ear constructs a full new face system, increasing its face count by one
and its total boundary length by twice the ear length. -/
theorem IsDrawing.exists_ear_faceSystem
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hBG : B ≤ G)
    (M : FaceSystem B drawing)
    {a b : Plane} {P : List β} (hpath : G.IsPath a P b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ P, g ∉ E(B)) :
    ∃ M' : FaceSystem (B.union (G.pathGraphOf a P)) drawing,
      M'.faceCount = M.faceCount + 1 ∧
      M'.boundaryLength = M.boundaryLength + 2 * P.length := by
  have hne : P ≠ [] := hpath.ne_nil hab
  obtain ⟨z₀, hz₀, hsub₀⟩ := h.exists_face_of_ear hBG hpath hab hint hnew
  obtain ⟨q, hq, hqface⟩ := M.exhaustive z₀ hz₀
  obtain ⟨z₁, e, u, v, D, hz₁, hqface₁, hface, hperm⟩ := M.valid q hq
  have hfaces : face B drawing z₀ = face B drawing z₁ :=
    hqface.symm.trans hqface₁
  have hsub₁ : edgesCover drawing P \ {a, b} ⊆ face B drawing z₁ := by
    rw [← hfaces]
    exact hsub₀
  obtain ⟨q₁, q₂, hv₁, hv₂, hq₁q₂, hpartition, hlength⟩ :=
    h.ear_face_split hpoly hBG hpath hab ha hb hint hnew hsub₁ hface
  have hsubq₁ : q₁.1 ⊆ q.1 := by
    rw [hqface₁]
    intro z hz
    exact (hpartition.symm ▸ Set.mem_union_left q₂.1 hz).1
  have hsubq₂ : q₂.1 ⊆ q.1 := by
    rw [hqface₁]
    intro z hz
    exact (hpartition.symm ▸ Set.mem_union_right q₁.1 hz).1
  have hsurvive : ∀ r ∈ M.boundaries, r ≠ q →
      IsBoundaryList (B.union (G.pathGraphOf a P)) drawing r.1 r.2 := by
    intro r hr hrq
    have hdisOld : Disjoint r.1 q.1 := M.disjoint_regions hr hq hrq
    have hdisFace : Disjoint r.1 (face B drawing z₁) := by
      rw [← hqface₁]
      exact hdisOld
    exact (M.valid r hr).mono_union_of_disjoint <|
      h.ear_disjoint_of_other_face hpath hab ha hb hsub₁ (M.valid r hr) hdisFace
  have hext : exterior (B.union (G.pathGraphOf a P)) drawing ⊆
      exterior B drawing := by
    rw [exterior_union]
    exact Set.inter_subset_left
  have hcover : ∀ z ∈ exterior (B.union (G.pathGraphOf a P)) drawing,
      z ∈ q.1 → z ∈ q₁.1 ∨ z ∈ q₂.1 := by
    intro z hz hzq
    have hz' := hz
    rw [exterior_union, h.pointSet_pathGraphOf hpath.isWalk hne] at hz'
    have hzDiff : z ∈ face B drawing z₁ \ edgesCover drawing P :=
      ⟨hqface₁.symm ▸ hzq, hz'.2⟩
    have hzUnion : z ∈ q₁.1 ∪ q₂.1 := hpartition ▸ hzDiff
    exact hzUnion
  obtain ⟨M', _hM', hcount, hweight⟩ := M.exists_replacement q q₁ q₂ hq
    hv₁ hv₂ hq₁q₂ hsubq₁ hsubq₂ hsurvive hext hcover
  refine ⟨M', hcount, ?_⟩
  have hremoved : q.2.length = (e :: D).length := hperm.length_eq
  omega

end Graph
