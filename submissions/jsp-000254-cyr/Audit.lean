import Erdos302Cambie

open Filter Topology

#print axioms erdos_302_five_eighths_explicit
#print axioms erdos_302_lower_five_eighths
#print axioms erdos_302_lower_half

/-- Cambie's construction with explicit error term. -/
example (N : ℕ) : ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ (5 * N : ℝ) / 8 - 2 ≤ A.card :=
  erdos_302_five_eighths_explicit N

/-- The formal-conjectures statements `erdos_302.variants.lower_five_eighths` and `lower_half`. -/
example (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((5 : ℝ) / 8 - ε) * N ≤ f N := erdos_302_lower_five_eighths f hf ε hε
example (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((1 : ℝ) / 2 - ε) * N ≤ f N := erdos_302_lower_half f hf ε hε

/-- The definitions are the formal-conjectures ones. -/
example (A : Finset ℕ) : NoUnitFractionTriple A ↔ ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c := Iff.rfl
