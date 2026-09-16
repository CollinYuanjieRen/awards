import Erdos1119Wetzel.Countable
import Erdos1119Wetzel.Recursion

/-!
# Wetzel's problem: Erdős's theorem

Wetzel asked whether a family of entire functions whose values at every point form a countable
set must itself be countable.  Erdős (Michigan Math. J. 11 (1964), 9–10) showed that the answer
depends on the continuum hypothesis: if `ℵ₁ < 𝔠` every such family is countable, and if
`𝔠 = ℵ₁` there is such a family of cardinality `𝔠`.  The first half is the vendored
`Erdos1119.erdos_1119`; the second half is `exists_uncountable_wetzelFamily_of_continuum_eq`.
-/

open Cardinal

/-- **Erdős (1964), answering Wetzel.**  There is an uncountable family of entire functions
taking only countably many values at every point if and only if the continuum hypothesis
`𝔠 = ℵ₁` holds. -/
theorem exists_uncountable_wetzelFamily_iff_continuum_eq_aleph_one :
    (∃ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) ∧
        (∀ z : ℂ, {y : ℂ | ∃ f ∈ F, f z = y}.Countable) ∧ ¬ F.Countable) ↔
      (𝔠 : Cardinal.{0}) = ℵ₁ := by
  constructor
  · rintro ⟨F, hF, hval, hunc⟩
    by_contra hne
    have hlt : (ℵ₁ : Cardinal.{0}) < 𝔠 := lt_of_le_of_ne aleph_one_le_continuum (Ne.symm hne)
    exact hunc (Erdos1119.erdos_1119 hlt F hF hval)
  · intro h
    exact exists_uncountable_wetzelFamily_of_continuum_eq h
