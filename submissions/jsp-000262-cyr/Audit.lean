import Erdos313Structure

open Erdos313

#print axioms erdos313_denominator_eq_prod
#print axioms erdos313_unique
#print axioms erdos313_structure_closed

/-- Erdős #313: in every solution the denominator is the product of the primes. -/
example {m : ℕ} {P : Finset ℕ} (h : (m, P) ∈ erdos313Solutions) : m = ∏ p ∈ P, p :=
  erdos313_denominator_eq_prod h

/-- Hence at most one solution per `m`. -/
example {m : ℕ} {P Q : Finset ℕ} (hP : (m, P) ∈ erdos313Solutions) (hQ : (m, Q) ∈ erdos313Solutions) :
    P = Q := erdos313_unique hP hQ

/-- The definition is the formal-conjectures one. -/
example (m : ℕ) (P : Finset ℕ) : (m, P) ∈ erdos313Solutions ↔
    (2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m) := Iff.rfl
