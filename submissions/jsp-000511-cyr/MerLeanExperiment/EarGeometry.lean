/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license.
Adapted from Schoenflies/FaceCyclesProof.lean at
05a43d29cde026618777db3d4e4316204ccca237, hasFaceCycles_union.
-/
import MerLeanExperiment.Vendor.Schoenflies.FaceCyclesLand

open scoped Graph
open Set Schoenflies

namespace Graph

/-- Splitting a genuine face boundary at an ear's endpoints produces the two
separating polygonal curves used by the exact crosscut theorem. -/
theorem IsDrawing.ear_split_geometry
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hBG : B ≤ G)
    {a b : Plane} {P : List β} (hpath : G.IsPath a P b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a P, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ P, g ∉ E(B))
    {z : Plane} (hsub : edgesCover drawing P \ {a, b} ⊆ face B drawing z)
    {e : β} {u v : Plane} {D : List β} (hface : IsFaceCycle B drawing z e u v D) :
    ∃ D₁ D₂ : List β,
      B.IsPath a D₁ b ∧ B.IsPath b D₂ a ∧ (D₁ ++ D₂).Perm (e :: D) ∧
      IsArcBetween (edgesCover drawing D₁) a b ∧
      IsArcBetween (edgesCover drawing D₂) b a ∧
      edgesCover drawing D₁ ∩ edgesCover drawing D₂ = {a, b} ∧
      edgesCover drawing D₁ ∪ edgesCover drawing D₂ = edgesCover drawing (e :: D) ∧
      edgesCover drawing P ∩ edgesCover drawing (e :: D) = {a, b} ∧
      IsSeparating (edgesCover drawing D₁ ∪ edgesCover drawing P) ∧
      IsSeparating (edgesCover drawing D₂ ∪ edgesCover drawing P) := by
  have : B.Finite := Graph.Finite.of_le hBG
  have hB : IsDrawing B drawing := h.mono hBG
  have hne : P ≠ [] := hpath.ne_nil hab
  have hPG : G.pathGraphOf a P ≤ G := pathGraphOf_le hpath.isWalk
  have hB'G : B.union (G.pathGraphOf a P) ≤ G := union_le hBG hPG
  have hB' : IsDrawing (B.union (G.pathGraphOf a P)) drawing := h.mono hB'G
  have hpoly' : ∀ g ∈ E(B.union (G.pathGraphOf a P)), IsPolygonal (edgeArc drawing g) :=
    fun g hg => hpoly g (hB'G.edgeSet_mono hg)
  have hParc : IsArcBetween (edgesCover drawing P) a b :=
    h.path_isArcBetween hpath hne
  have hopenF : IsOpen (face B drawing z) := hB.isOpen_face z
  obtain ⟨haF, hbF⟩ := h.ends_mem_frontier_face hopenF hpath hab ha hb hsub
  have hfr : frontier (face B drawing z) = edgesCover drawing (e :: D) :=
    hface.frontier_eq
  have haW : a ∈ B.walkVertices u D :=
    hB.mem_walkVertices_of_mem_edgesCover hface.isCycle ha (hfr ▸ haF)
  have hbW : b ∈ B.walkVertices u D :=
    hB.mem_walkVertices_of_mem_edgesCover hface.isCycle hb (hfr ▸ hbF)
  obtain ⟨D₁, D₂, hD₁, hD₂, hperm, hmeet⟩ :=
    hface.isCycle.split_at haW hbW hab
  have hnodup : (e :: D).Nodup := List.nodup_cons.2 ⟨hface.isCycle.notMem,
    hface.isCycle.isPath.nodup⟩
  have hdisj : ∀ g ∈ D₁, g ∉ D₂ := fun g hg hg₂ =>
    (List.nodup_append.1 (hperm.nodup_iff.2 hnodup)).2.2 g hg g hg₂ rfl
  obtain ⟨harc₁, harc₂, hinter⟩ :=
    hB.arcs_of_split hD₁ hD₂ hab hdisj hmeet
  have hunion : edgesCover drawing D₁ ∪ edgesCover drawing D₂ =
      edgesCover drawing (e :: D) := by
    rw [← edgesCover_append, edgesCover_perm hperm]
  have hJsub : edgesCover drawing (e :: D) ⊆ pointSet B drawing :=
    edgesCover_subset_pointSet fun g hg => by
      rcases List.mem_cons.1 hg with rfl | hg'
      · exact hface.isCycle.isLink.edge_mem
      · exact hface.isCycle.isPath.edge_mem hg'
  have hmeetJ : edgesCover drawing P ∩ edgesCover drawing (e :: D) = {a, b} := by
    refine Set.Subset.antisymm (fun w hw =>
      h.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hJsub hw.2⟩) ?_
    rintro w (rfl | rfl)
    · exact ⟨hParc.left_mem, hfr ▸ haF⟩
    · exact ⟨hParc.right_mem, hfr ▸ hbF⟩
  obtain ⟨f₁, x₁, y₁, T₁, hcyc₁, hperm₁⟩ :=
    exists_spliced_cycle hBG hD₁ hpath hab hnew hint
  have hsep₁ : IsSeparating (edgesCover drawing D₁ ∪ edgesCover drawing P) := by
    have hcov : edgesCover drawing (f₁ :: T₁) =
        edgesCover drawing D₁ ∪ edgesCover drawing P := by
      rw [edgesCover_perm hperm₁, edgesCover_append]
    rw [← hcov]
    exact hB'.cycle_isSeparating hpoly' hcyc₁
  obtain ⟨f₂, x₂, y₂, T₂, hcyc₂, hperm₂⟩ :=
    exists_spliced_cycle hBG hD₂.reverse hpath hab hnew hint
  have hsep₂ : IsSeparating (edgesCover drawing D₂ ∪ edgesCover drawing P) := by
    have hcov : edgesCover drawing (f₂ :: T₂) =
        edgesCover drawing D₂ ∪ edgesCover drawing P := by
      rw [edgesCover_perm hperm₂, edgesCover_append, edgesCover_reverse]
    rw [← hcov]
    exact hB'.cycle_isSeparating hpoly' hcyc₂
  exact ⟨D₁, D₂, hD₁, hD₂, hperm, harc₁, harc₂, hinter, hunion,
    hmeetJ, hsep₁, hsep₂⟩

end Graph
