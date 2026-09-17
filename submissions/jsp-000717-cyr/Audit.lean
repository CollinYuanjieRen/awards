import Erdos865K2

open Finset

#print axioms erdos_865_k2
#print axioms erdos_865_k2_closed

/-- Erdős #865, the `k = 2` case (the formal-conjectures statement `erdos_865.variants.k2`). -/
example (N : ℕ) : ∀ A ⊆ Icc 1 (2 * N), A.card ≥ N + 2 →
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b ∈ A := erdos_865_k2 N
