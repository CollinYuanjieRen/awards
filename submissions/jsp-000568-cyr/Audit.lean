import Erdos697TrivialBound

open Filter Set Real
open scoped Topology

#print axioms Erdos697.density_exists
#print axioms erdos_697_delta_lt_succ
#print axioms Erdos697.erdos_697_delta_lt

/-- Erdős #697: the density δ(m, α) exists, in the formal-conjectures shape `density_exists`. -/
example (m : ℕ) (α : ℝ) : ∃ δ, HasDensity
    {n : ℕ | ∃ d, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Set.Ioo 1 (exp (m ^ α)) ∧ d ∣ n} δ :=
  Erdos697.density_exists m α

/-- The trivial bound in the formal-conjectures shape `erdos_697.variants.delta_lt`, for `1 ≤ m`. -/
example (m : ℕ) (hm : 1 ≤ m) (α : ℝ) : Erdos697.δ m α < (m ^ α + 1) / m :=
  Erdos697.erdos_697_delta_lt m hm α

/-- The definitions are the formal-conjectures ones. -/
example {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] (S : Set β) (α : ℝ) (A : Set β) :
    Set.HasDensity S α A ↔ Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α) := Iff.rfl
example (m : ℕ) (α : ℝ) : Erdos697.δ m α = (Erdos697.density_exists m α).choose := rfl
