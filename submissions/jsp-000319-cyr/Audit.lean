import Erdos386Examples

#print axioms erdos_386_examples_closed
#print axioms Erdos386.exists_middle_consecutivePrimeProduct
#print axioms Erdos386.choose_two_examples

/-- Erdős #386: `C(7, 3)` is a product of consecutive primes. -/
example : ∃ p q : ℕ, (7).choose 3 = ∏ i ∈ Finset.Ico p q, Nat.nth Nat.Prime i :=
  erdos_386_examples_closed.1
