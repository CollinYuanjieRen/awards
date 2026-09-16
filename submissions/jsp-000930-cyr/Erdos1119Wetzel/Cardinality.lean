import Erdos1119Wetzel.Recursion

/-!
# Erdős's literal conclusion: a family of power `𝔠`

Erdős states the continuum-hypothesis half as "some family with property `P₀` has the power
`𝔠`".  The family `Set.range (fam e)` built in `Recursion.lean` is indexed injectively by
`Omega1`, so its cardinality is `ℵ₁ = 𝔠`.
-/

open Cardinal Set

/-- If `𝔠 = ℵ₁`, there is a family of entire functions of cardinality `𝔠` taking only countably
many values at every point. -/
theorem exists_wetzelFamily_card_continuum (h : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) ∧
      (∀ z : ℂ, {y : ℂ | ∃ f ∈ F, f z = y}.Countable) ∧ #F = 𝔠 := by
  obtain ⟨e⟩ := nonempty_equiv_complex h
  refine ⟨Set.range (fam e), ?_, fun z ↦ ?_, ?_⟩
  · rintro _ ⟨γ, rfl⟩
    exact (fam_spec e γ).1
  · obtain ⟨α, rfl⟩ : ∃ α : Omega1, e α = z := ⟨e.symm z, e.apply_symm_apply z⟩
    have hsub : {y : ℂ | ∃ f ∈ Set.range (fam e), f (e α) = y} ⊆
        rationalLattice ∪ (fun γ : Omega1 ↦ fam e γ (e α)) '' Iic α := by
      rintro y ⟨f, ⟨γ, rfl⟩, rfl⟩
      rcases lt_or_ge α γ with hlt | hle
      · exact Or.inl ((fam_spec e γ).2.1 α hlt)
      · exact Or.inr ⟨γ, hle, rfl⟩
    exact (rationalLattice_countable.union ((countable_Iic α).image _)).mono hsub
  · rw [Cardinal.mk_range_eq _ (fam_injective e), mk_omega1, h]
