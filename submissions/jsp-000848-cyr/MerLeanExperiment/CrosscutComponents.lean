import MerLeanExperiment.CrosscutRegions

open Set
namespace Schoenflies

/-- Matching actual components of a region partition. -/
theorem component_eq_one_of_two_regions
    {J₁ J₂ W₁ V₁ W₂ V₂ S T : Set Plane}
    (hWV₁ : IsRegionPair J₁ W₁ V₁)
    (hWV₂ : IsRegionPair J₂ W₂ V₂)
    (hSne : S.Nonempty)
    (hSW₁ : S ⊆ W₁) (hSW₂ : S ⊆ W₂)
    (hTS : Disjoint T S)
    (hexhaust : ∀ z ∈ T,
      IsRegionOf J₁ (connectedComponentIn T z) ∨
      IsRegionOf J₂ (connectedComponentIn T z)) :
    ∀ z ∈ T,
      connectedComponentIn T z = V₁ ∨
      connectedComponentIn T z = V₂ := by
  intro z hz
  have hcomponent : Disjoint (connectedComponentIn T z) S :=
    hTS.mono (connectedComponentIn_subset T z) Subset.rfl
  rcases hexhaust z hz with hregion | hregion
  · exact Or.inl <|
      region_eq_right_of_disjoint hWV₁ hregion hSne hSW₁ hcomponent
  · exact Or.inr <|
      region_eq_right_of_disjoint hWV₂ hregion hSne hSW₂ hcomponent

/-- Matching actual components of a region partition. -/
theorem eq_union_and_disjoint_of_two_components
    {T V₁ V₂ : Set Plane}
    (hV₁ : V₁ ⊆ T) (hV₂ : V₂ ⊆ T)
    (hc₁ : ∀ z ∈ V₁, connectedComponentIn T z = V₁)
    (hc₂ : ∀ z ∈ V₂, connectedComponentIn T z = V₂)
    (hne : V₁ ≠ V₂)
    (hexhaust : ∀ z ∈ T,
      connectedComponentIn T z = V₁ ∨
      connectedComponentIn T z = V₂) :
    T = V₁ ∪ V₂ ∧ Disjoint V₁ V₂ := by
  constructor
  · apply Set.Subset.antisymm
    · intro z hz
      have hzcomponent : z ∈ connectedComponentIn T z :=
        mem_connectedComponentIn hz
      rcases hexhaust z hz with hcomponent | hcomponent
      · exact Or.inl (hcomponent ▸ hzcomponent)
      · exact Or.inr (hcomponent ▸ hzcomponent)
    · intro z hz
      rcases hz with hz | hz
      · exact hV₁ hz
      · exact hV₂ hz
  · rw [Set.disjoint_left]
    intro z hz₁ hz₂
    apply hne
    calc
      V₁ = connectedComponentIn T z := (hc₁ z hz₁).symm
      _ = V₂ := hc₂ z hz₂

end Schoenflies
