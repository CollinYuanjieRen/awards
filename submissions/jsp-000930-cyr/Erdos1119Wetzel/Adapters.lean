import Mathlib

/-!
# Intended-model adapter for the continuum hypothesis

The right-hand side of the target, `𝔠 = ℵ₁`, is Mathlib's continuum hypothesis for
`Cardinal.{0}`.  Since `ℵ₁ ≤ 𝔠` is a theorem, it is equivalent to the negation of `ℵ₁ < 𝔠`, the
hypothesis of the vendored countable half.  This consistency lemma is not used by the main
theorem's proof.
-/

open Cardinal

/-- The continuum hypothesis is the negation of `ℵ₁ < 𝔠`. -/
theorem continuum_eq_aleph_one_iff_not_lt : (𝔠 : Cardinal.{0}) = ℵ₁ ↔ ¬ (ℵ₁ : Cardinal.{0}) < 𝔠 := by
  constructor
  · intro h hlt
    exact absurd h (ne_of_gt hlt)
  · intro h
    exact (le_antisymm (not_lt.1 h) aleph_one_le_continuum)
