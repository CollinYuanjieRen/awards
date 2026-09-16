import Erdos1119Wetzel.RationalLattice
import Erdos1119Wetzel.Interpolation
import Erdos1119Wetzel.IndexType

/-!
# Erdős's transfinite construction

Assume `𝔠 = ℵ₁` and fix a bijection `e : Omega1 ≃ ℂ`.  By transfinite recursion along the
well-order of `Omega1`, choose for every `γ` an entire function `fam γ` such that
`fam γ (e β) ∈ rationalLattice` for all `β < γ` and `fam γ ≠ fam β` for all `β < γ`; this is
possible because the initial segment `{β | β < γ}` is countable, so `exists_entire_interpolant`
applies to an injective enumeration of `e '' Iio γ ∪ ℕ` and a surjective enumeration of the
earlier functions.  Then `F = range fam` has cardinality `ℵ₁ = 𝔠`, hence is uncountable, and for
every `z = e α` the values `fam γ z` lie in `rationalLattice` for `γ > α` and form a countable set
for `γ ≤ α`.
-/

open Cardinal Set

/-- The recursion step: given the earlier functions, an entire function taking Gaussian-rational
values on `e '' Iio γ` and different from every earlier function exists. -/
theorem exists_step (e : Omega1 ≃ ℂ) (γ : Omega1) (prev : ∀ β : Omega1, β < γ → (ℂ → ℂ)) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ β : Omega1, (hβ : β < γ) → f (e β) ∈ rationalLattice) ∧
      ∀ β : Omega1, (hβ : β < γ) → f ≠ prev β hβ := by
  obtain ⟨hTc, hTi⟩ := countable_infinite_union_nat ((countable_Iio γ).image e)
  obtain ⟨w, hw, hwrange⟩ := exists_injective_enumeration hTc hTi
  have : Countable (Iio γ) := (countable_Iio γ).to_subtype
  obtain ⟨g, hg⟩ :=
    exists_surjective_enumeration (Set.countable_range fun β : Iio γ ↦ prev β.1 β.2)
  obtain ⟨f, hfd, hfn⟩ := exists_entire_interpolant hw g rationalLattice
    fun c δ hδ v ↦ rationalLattice_dense_punctured c hδ v
  refine ⟨f, hfd, fun β hβ ↦ ?_, fun β hβ hcon ↦ ?_⟩
  · obtain ⟨n, hn⟩ : e β ∈ Set.range w := by
      rw [hwrange]
      exact Or.inl ⟨β, hβ, rfl⟩
    rw [← hn]
    exact (hfn n).1
  · obtain ⟨n, hn⟩ := hg (Set.mem_range_self (⟨β, hβ⟩ : Iio γ))
    exact (hfn n).2 (by rw [hcon, ← hn])

/-- The transfinite family of entire functions obtained by iterating `exists_step` along the
well-order of `Omega1`. -/
noncomputable def fam (e : Omega1 ≃ ℂ) : Omega1 → (ℂ → ℂ) :=
  WellFounded.fix wellFounded_lt fun γ ih ↦ Classical.choose (exists_step e γ ih)

/-- The defining property of `fam`: it is entire, takes Gaussian-rational values on the earlier
points `e β`, and differs from every earlier member of the family. -/
theorem fam_spec (e : Omega1 ≃ ℂ) (γ : Omega1) :
    Differentiable ℂ (fam e γ) ∧
      (∀ β : Omega1, (hβ : β < γ) → fam e γ (e β) ∈ rationalLattice) ∧
        ∀ β : Omega1, (hβ : β < γ) → fam e γ ≠ fam e β := by
  rw [fam, WellFounded.fix_eq]
  exact Classical.choose_spec (exists_step e γ _)

/-- Distinct indices give distinct functions, so `fam e` is injective. -/
theorem fam_injective (e : Omega1 ≃ ℂ) : Function.Injective (fam e) := by
  intro β γ hbg
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (fam_spec e γ).2.2 β hlt hbg.symm
  · exact (fam_spec e β).2.2 γ hlt hbg

/-- **Erdős's theorem, the continuum-hypothesis half.**  If `𝔠 = ℵ₁`, there is an uncountable
family of entire functions taking only countably many values at every point. -/
theorem exists_uncountable_wetzelFamily_of_continuum_eq (h : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) ∧
      (∀ z : ℂ, {y : ℂ | ∃ f ∈ F, f z = y}.Countable) ∧ ¬ F.Countable := by
  obtain ⟨e⟩ := nonempty_equiv_complex h
  refine ⟨Set.range (fam e), ?_, fun z ↦ ?_, fun hc ↦ ?_⟩
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
  · refine not_countable_omega1 ?_
    have hpre : (fam e ⁻¹' Set.range (fam e)).Countable := hc.preimage (fam_injective e)
    have huniv : fam e ⁻¹' Set.range (fam e) = (Set.univ : Set Omega1) := by
      ext γ
      simp
    rwa [huniv] at hpre
