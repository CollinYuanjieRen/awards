import Erdos374NoPrime

open scoped Nat

#print axioms not_isFactorialSquareSet_of_prime
#print axioms erdos_374_prime_notMem_D
#print axioms erdos_374_closed

/-- Erdős #374: no `D_k` contains a prime. -/
example (p k : ℕ) (hp : p.Prime) : p ∉ D k := erdos_374_prime_notMem_D p k hp

/-- The definitions, unfolded. -/
example (m : ℕ) (s : Finset ℕ) :
    IsFactorialSquareSet m s ↔ (m ∈ s ∧ (∀ a ∈ s, a ≤ m) ∧ IsSquare (∏ a ∈ s, a !)) := Iff.rfl
example (k : ℕ) (m : ℕ) : m ∈ D k ↔
    ((∃ s : Finset ℕ, s.card = k ∧ IsFactorialSquareSet m s) ∧ F m = k) := Iff.rfl
