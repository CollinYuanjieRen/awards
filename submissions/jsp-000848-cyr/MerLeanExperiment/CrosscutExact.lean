import MerLeanExperiment.CrosscutComponents
import MerLeanExperiment.Vendor.Schoenflies.FaceCyclesLand

open Set
namespace Schoenflies

/-- A crosscut splits either old region into exactly two actual components. -/
theorem crosscut_exactly_two_components
    {J A₁ A₂ P Ω : Set Plane} {p q : Plane}
    (hJ : IsSeparating J)
    (hJpoly : IsPolygonal J) (hPpoly : IsPolygonal P)
    (hA₁ : IsArcBetween A₁ p q) (hA₂ : IsArcBetween A₂ p q)
    (hunion : A₁ ∪ A₂ = J)
    (hinter : A₁ ∩ A₂ = {p, q})
    (hP : IsArcBetween P p q) (hPJ : P ∩ J = {p, q})
    (hΩ : IsRegionOf J Ω) (hPsub : P \ {p, q} ⊆ Ω)
    (hJ₁ : IsSeparating (A₁ ∪ P))
    (hJ₂ : IsSeparating (A₂ ∪ P)) :
    ∃ V₁ V₂ : Set Plane,
      IsRegionOf (A₁ ∪ P) V₁ ∧ IsRegionOf (A₂ ∪ P) V₂ ∧
      V₁.Nonempty ∧ V₂.Nonempty ∧ V₁ ≠ V₂ ∧
      Ω \ P = V₁ ∪ V₂ ∧ Disjoint V₁ V₂ ∧
      (∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁) ∧
      (∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂) ∧
      frontier V₁ = A₁ ∪ P ∧ frontier V₂ = A₂ ∪ P := by
  have hA₁J : A₁ ⊆ J := by
    rw [← hunion]
    exact Set.subset_union_left
  have hA₂J : A₂ ⊆ J := by
    rw [← hunion]
    exact Set.subset_union_right
  have hends : ({p, q} : Set Plane) ⊆ J := by
    rintro z (rfl | rfl)
    · exact hA₁J hA₁.left_mem
    · exact hA₁J hA₁.right_mem
  have hendsA₁ : ({p, q} : Set Plane) ⊆ A₁ := by
    rintro z (rfl | rfl)
    · exact hA₁.left_mem
    · exact hA₁.right_mem
  have hendsA₂ : ({p, q} : Set Plane) ⊆ A₂ := by
    rintro z (rfl | rfl)
    · exact hA₂.left_mem
    · exact hA₂.right_mem
  have hP₁ : P ∩ J ⊆ A₁ := by
    rw [hPJ]
    exact hendsA₁
  have hP₂ : P ∩ J ⊆ A₂ := by
    rw [hPJ]
    exact hendsA₂
  have hA₁ne : A₁ ≠ A₂ := by
    apply arcs_ne (le_of_eq hinter)
    obtain ⟨z, hzA₁, hzends⟩ := hA₁.nonempty_diff
    exact fun hsub => hzends (hsub hzA₁)
  obtain ⟨Ω', hΩpair⟩ : ∃ Ω' : Set Plane, IsRegionPair J Ω Ω' := by
    rcases hΩ with hΩ | hΩ
    · exact ⟨outside J, Or.inl ⟨hΩ, rfl⟩⟩
    · exact ⟨inside J, Or.inr ⟨hΩ, rfl⟩⟩
  have hΩ'conn := hΩpair.right.isConnected hJ
  have hΩ'A₁P : Disjoint Ω' (A₁ ∪ P) :=
    oppositeRegion_disjoint_crosscut_curve hΩpair hA₁J hends hPsub
  have hΩ'A₂P : Disjoint Ω' (A₂ ∪ P) :=
    oppositeRegion_disjoint_crosscut_curve hΩpair hA₂J hends hPsub
  obtain ⟨W₁, V₁, hWV₁, hΩW₁⟩ :=
    hJ₁.exists_isRegionPair_subset hΩ'conn.isPreconnected hΩ'conn.nonempty hΩ'A₁P
  obtain ⟨W₂, V₂, hWV₂, hΩW₂⟩ :=
    hJ₂.exists_isRegionPair_subset hΩ'conn.isPreconnected hΩ'conn.nonempty hΩ'A₂P
  obtain ⟨⟨hV₁sub, hc₁⟩, ⟨hV₂sub, hc₂⟩, hVne, -, -⟩ :=
    crosscut_cells hJ hJ₁ hJ₂ hA₁J hA₂J hP₁ hP₂ hA₁ne hΩpair
      hWV₁ hΩW₁ hWV₂ hΩW₂
  have hexhaust :=
    crosscutSplitsRegion J A₁ A₂ P Ω p q hJ hJpoly hPpoly hA₁ hA₂ hunion hinter
      hP hPJ hΩpair.left hPsub
  have hdiff : Disjoint (Ω \ P) Ω' :=
    hΩpair.disjoint.mono sdiff_subset Subset.rfl
  have hcomponents := component_eq_one_of_two_regions hWV₁ hWV₂ hΩ'conn.nonempty
    hΩW₁ hΩW₂ hdiff hexhaust
  obtain ⟨hpartition, hVdisjoint⟩ :=
    eq_union_and_disjoint_of_two_components hV₁sub hV₂sub hc₁ hc₂ hVne hcomponents
  exact ⟨V₁, V₂, hWV₁.right, hWV₂.right,
    (hWV₁.right.isConnected hJ₁).nonempty, (hWV₂.right.isConnected hJ₂).nonempty,
    hVne, hpartition, hVdisjoint, hc₁, hc₂,
    hWV₁.right.frontier_eq hJ₁, hWV₂.right.frontier_eq hJ₂⟩

end Schoenflies
