import Erdos885KnownCases

#print axioms erdos_885_k_two_and_three
#print axioms erdos_885_k_eq_2
#print axioms erdos_885_k_eq_3

/-- Erdős #885, `k = 2` and `k = 3`, in the formal-conjectures shapes of
`erdos_885.variants.k_eq_2` and `k_eq_3`. -/
example : ∃ Ns : Finset ℕ, (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = 2 ∧
    (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2 := erdos_885_k_eq_2
example : ∃ Ns : Finset ℕ, (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = 3 ∧
    (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3 := erdos_885_k_eq_3

/-- The definition is the formal-conjectures one. -/
example (n d : ℕ) : d ∈ factorDifferenceSet n ↔ ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b| :=
  Iff.rfl
