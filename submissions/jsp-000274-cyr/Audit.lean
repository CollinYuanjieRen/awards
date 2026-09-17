import Erdos329SidonDensity

open Function Set Filter

#print axioms erdos_329_lower_bound
#print axioms erdosTuranSet_isSidon

/-- Erdős #329, Erdős's lower bound 1/2, in the formal-conjectures shape
`erdos_329.variants.lower_bound`. -/
example : ∃ (A : Set ℕ), IsSidon A ∧ sidonUpperDensity A ≥ 1/2 := erdos_329_lower_bound

/-- The definitions are the formal-conjectures ones. -/
example (A : Set ℕ) : sidonUpperDensity A = limsup (fun N => sqrtPartialDensity A N) atTop := rfl
example {α : Type*} [AddCommMonoid α] (A : Set α) : IsSidon A ↔ ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁) := Iff.rfl
