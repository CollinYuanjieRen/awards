import Erdos830Amicable

open scoped ArithmeticFunction.sigma

#print axioms erdos_830_example
#print axioms erdos_830_example_closed

/-- Erdős #830: `220` and `284` form an amicable pair. -/
example : IsAmicable 220 284 := erdos_830_example

/-- The structure is the formal-conjectures one. -/
example (a b : ℕ) : IsAmicable a b ↔ σ 1 a = a + b ∧ σ 1 b = a + b ∧ a ≠ b := isAmicable_iff a b
