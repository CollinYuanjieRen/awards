import MerLeanExperiment.EarGeometry
import MerLeanExperiment.CrosscutExact
import MerLeanExperiment.SplicedBoundary

open scoped Graph
open Set Schoenflies

namespace Graph

/-- The affected old face splits into two actual new faces with the exact edge-length balance. -/
theorem IsDrawing.ear_face_split
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hBG : B ≤ G)
    {a b : Plane} {P : List β} (hpath : G.IsPath a P b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ P, g ∉ E(B))
    {z : Plane} (hsub : edgesCover drawing P \ {a, b} ⊆ face B drawing z)
    {e : β} {u v : Plane} {D : List β} (hface : IsFaceCycle B drawing z e u v D) :
    ∃ q₁ q₂ : Set Plane × List β,
      IsBoundaryList (B.union (G.pathGraphOf a P)) drawing q₁.1 q₁.2 ∧
      IsBoundaryList (B.union (G.pathGraphOf a P)) drawing q₂.1 q₂.2 ∧
      q₁.1 ≠ q₂.1 ∧
      face B drawing z \ edgesCover drawing P = q₁.1 ∪ q₂.1 ∧
      q₁.2.length + q₂.2.length = (e :: D).length + 2 * P.length := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hperm, harc₁, harc₂, hinter, hunion,
      hmeet, hsep₁, hsep₂⟩ :=
    h.ear_split_geometry hpoly hBG hpath hab ha hb hint hnew hsub hface
  have hne : P ≠ [] := hpath.ne_nil hab
  have hPArc : IsArcBetween (edgesCover drawing P) a b :=
    h.path_isArcBetween hpath hne
  have hJpoly : IsPolygonal (edgesCover drawing (e :: D)) :=
    h.isPolygonal_edgesCover hpoly (hface.isCycle.isWalk_cons.mono hBG)
      (List.cons_ne_nil e D)
  have hPpoly : IsPolygonal (edgesCover drawing P) :=
    h.isPolygonal_edgesCover hpoly hpath.isWalk hne
  obtain ⟨U₁, U₂, hreg₁, hreg₂, hU₁ne, hU₂ne, hUne, hpartition,
      hUdisj, hc₁, hc₂, hfront₁, hfront₂⟩ :=
    crosscut_exactly_two_components hface.isSeparating hJpoly hPpoly harc₁
      harc₂.reverse hunion hinter hPArc hmeet hface.isRegionOf hsub hsep₁ hsep₂
  have hU₁sub : U₁ ⊆ face B drawing z \ edgesCover drawing P := by
    rw [hpartition]
    exact Set.subset_union_left
  have hU₂sub : U₂ ⊆ face B drawing z \ edgesCover drawing P := by
    rw [hpartition]
    exact Set.subset_union_right
  have hboundary₁ : IsBoundaryList (B.union (G.pathGraphOf a P)) drawing
      U₁ (D₁ ++ P) :=
    h.spliced_boundaryList hpoly hBG hD₁ hpath hab hnew hint hU₁ne hU₁sub hc₁ hreg₁
  have hboundary₂ : IsBoundaryList (B.union (G.pathGraphOf a P)) drawing
      U₂ (D₂.reverse ++ P) := by
    apply h.spliced_boundaryList hpoly hBG hD₂.reverse hpath hab hnew hint
      hU₂ne hU₂sub hc₂
    simpa only [edgesCover_reverse] using hreg₂
  have hlength : D₁.length + D₂.length = (e :: D).length := by
    simpa only [List.length_append] using hperm.length_eq
  refine ⟨(U₁, D₁ ++ P), (U₂, D₂.reverse ++ P), hboundary₁, hboundary₂,
    hUne, hpartition, ?_⟩
  simp only [List.length_append, List.length_reverse]
  omega

end Graph
