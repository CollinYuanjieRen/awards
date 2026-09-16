import Mathlib

/-!
# The index type `ω₁` and countable enumerations

Under the continuum hypothesis the complex numbers can be well-ordered so that every initial
segment is countable: we index them by `(ℵ₁).ord.ToType`, a well-ordered type of cardinality
`ℵ₁` all of whose initial segments have cardinality `< ℵ₁`, hence are countable.  We also record
the enumeration facts used in the transfinite construction.
-/

open Cardinal Set

/-- The index type: the well-ordered type of order type `ω₁`. -/
abbrev Omega1 : Type :=
  (ℵ₁ : Cardinal.{0}).ord.ToType

/-- `Omega1` has cardinality `ℵ₁`. -/
theorem mk_omega1 : #Omega1 = ℵ₁ :=
  Cardinal.mk_ord_toType _

/-- Every initial segment `{β | β < γ}` of `Omega1` is countable. -/
theorem countable_Iio (γ : Omega1) : (Iio γ).Countable := by
  have h : #(Iio γ) < (ℵ₁ : Cardinal.{0}) := by simpa using Cardinal.mk_Iio_lt γ
  exact Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp h)

/-- Every closed initial segment `{β | β ≤ γ}` of `Omega1` is countable. -/
theorem countable_Iic (γ : Omega1) : (Iic γ).Countable := by
  rw [← Set.Iio_insert]
  exact (countable_Iio γ).insert γ

/-- `Omega1` is uncountable. -/
theorem not_countable_omega1 : ¬ (Set.univ : Set Omega1).Countable := by
  intro h
  have h' : #Omega1 ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr (Set.countable_univ_iff.mp h)
  rw [mk_omega1] at h'
  exact absurd h' (not_le_of_gt Cardinal.aleph0_lt_aleph_one)

/-- Under the continuum hypothesis, `ℂ` is in bijection with `Omega1`. -/
theorem nonempty_equiv_complex (h : (𝔠 : Cardinal.{0}) = ℵ₁) : Nonempty (Omega1 ≃ ℂ) :=
  Cardinal.eq.mp (mk_omega1.trans (h.symm.trans Cardinal.mk_complex.symm))

/-- A countable infinite set of complex numbers is the range of an injective sequence. -/
theorem exists_injective_enumeration {T : Set ℂ} (hc : T.Countable) (hi : T.Infinite) :
    ∃ w : ℕ → ℂ, Function.Injective w ∧ Set.range w = T := by
  have : Countable T := hc.to_subtype
  have : Infinite T := hi.to_subtype
  obtain ⟨d⟩ := nonempty_denumerable T
  obtain ⟨e⟩ : Nonempty (T ≃ ℕ) := ⟨@Denumerable.eqv T d⟩
  refine ⟨fun n ↦ ((e.symm n : T) : ℂ), Subtype.val_injective.comp e.symm.injective, ?_⟩
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    exact (e.symm n).2
  · intro hz
    exact ⟨e ⟨z, hz⟩, by simp⟩

/-- A countable set of functions is contained in the range of a sequence. -/
theorem exists_surjective_enumeration {G : Set (ℂ → ℂ)} (hc : G.Countable) :
    ∃ g : ℕ → ℂ → ℂ, G ⊆ Set.range g := by
  rcases G.eq_empty_or_nonempty with hG | hG
  · exact ⟨fun _ _ ↦ 0, by simp [hG]⟩
  · obtain ⟨g, hg⟩ := hc.exists_eq_range hG
    exact ⟨g, hg.le⟩

/-- The set `T ∪ ℕ` (naturals as complex numbers) is countable and infinite whenever `T` is
countable. -/
theorem countable_infinite_union_nat {T : Set ℂ} (hc : T.Countable) :
    (T ∪ Set.range (fun n : ℕ ↦ (n : ℂ))).Countable ∧
      (T ∪ Set.range (fun n : ℕ ↦ (n : ℂ))).Infinite := by
  refine ⟨hc.union (Set.countable_range _), ?_⟩
  exact Set.Infinite.mono Set.subset_union_right
    (Set.infinite_range_of_injective (fun a b hab ↦ by exact_mod_cast hab))
