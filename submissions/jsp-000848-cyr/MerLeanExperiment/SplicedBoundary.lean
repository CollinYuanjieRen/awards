import MerLeanExperiment.FaceSystem

open scoped Graph
open Set Schoenflies

namespace Graph

/-- A component cut from an old face is the actual face bounded by its spliced cycle. -/
theorem IsDrawing.spliced_boundaryList
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hBG : B ≤ G)
    {a b : Plane} {A P : List β} (hA : B.IsPath a A b) (hpath : G.IsPath a P b)
    (hab : a ≠ b) (hnew : ∀ g ∈ P, g ∉ E(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B))
    {z : Plane} {U : Set Plane} (hUne : U.Nonempty)
    (hsub : U ⊆ face B drawing z \ edgesCover drawing P)
    (hc : ∀ w ∈ U,
      connectedComponentIn (face B drawing z \ edgesCover drawing P) w = U)
    (hregion : IsRegionOf (edgesCover drawing A ∪ edgesCover drawing P) U) :
    IsBoundaryList (B.union (G.pathGraphOf a P)) drawing U (A ++ P) := by
  obtain ⟨f, x, y, T, hcyc, hperm⟩ :=
    exists_spliced_cycle hBG hA hpath hab hnew hint
  let H := B.union (G.pathGraphOf a P)
  have hPG : G.pathGraphOf a P ≤ G := pathGraphOf_le hpath.isWalk
  have hHG : H ≤ G := union_le hBG hPG
  have hH : IsDrawing H drawing := h.mono hHG
  have hpolyH : ∀ g ∈ E(H), IsPolygonal (edgeArc drawing g) :=
    fun g hg => hpoly g (hHG.edgeSet_mono hg)
  have hne : P ≠ [] := hpath.ne_nil hab
  have hext : exterior H drawing = exterior B drawing \ edgesCover drawing P := by
    rw [exterior_union, h.pointSet_pathGraphOf hpath.isWalk hne]
  obtain ⟨w, hwU⟩ := hUne
  obtain ⟨hwface, hwP⟩ := hsub hwU
  have hwext : w ∈ exterior H drawing := by
    rw [hext]
    exact ⟨face_subset_exterior B drawing z hwface, hwP⟩
  have holdface : face B drawing w = face B drawing z :=
    (connectedComponentIn_eq hwface).symm
  change connectedComponentIn (exterior B drawing) w = face B drawing z at holdface
  have hface : face H drawing w = U := by
    have hstep : face H drawing w =
        connectedComponentIn (exterior B drawing \ edgesCover drawing P) w := by
      rw [face, hext]
    rw [hstep, Schoenflies.connectedComponentIn_diff, holdface]
    exact hc w hwU
  have hcover : edgesCover drawing (f :: T) =
      edgesCover drawing A ∪ edgesCover drawing P := by
    rw [edgesCover_perm hperm, edgesCover_append]
  have hfaceCycle : IsFaceCycle H drawing w f x y T := by
    refine ⟨hcyc, hH.cycle_isSeparating hpolyH hcyc, ?_⟩
    rw [hcover, hface]
    exact hregion
  exact ⟨w, f, x, y, T, hwext, hface.symm, hfaceCycle, hperm.symm⟩

end Graph
