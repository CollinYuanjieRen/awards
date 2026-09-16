import Erdos1119Wetzel

open Cardinal

#print axioms exists_uncountable_wetzelFamily_iff_continuum_eq_aleph_one
#print axioms exists_uncountable_wetzelFamily_of_continuum_eq
#print axioms exists_wetzelFamily_card_continuum
#print axioms Erdos1119.erdos_1119
#print axioms exists_entire_interpolant
#print axioms nodeSeries_differentiable

/-- The exact statement: an uncountable family of entire functions with countably many values
at every point exists if and only if the continuum hypothesis holds. -/
example :
    (∃ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) ∧
        (∀ z : ℂ, {y : ℂ | ∃ f ∈ F, f z = y}.Countable) ∧ ¬ F.Countable) ↔
      (𝔠 : Cardinal.{0}) = ℵ₁ :=
  exists_uncountable_wetzelFamily_iff_continuum_eq_aleph_one

/-- Erdős's literal continuum-hypothesis conclusion: a family of power `𝔠`. -/
example (h : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) ∧
      (∀ z : ℂ, {y : ℂ | ∃ f ∈ F, f z = y}.Countable) ∧ #F = 𝔠 :=
  exists_wetzelFamily_card_continuum h
