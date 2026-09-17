import Erdos542Examples

open Erdos542

#print axioms erdos_542_examples_closed
#print axioms Erdos542.two_three_five

/-- Erdős #542: `{2, 3, 5}` is admissible for `n = 5` with reciprocal sum `31/30`. -/
example : IsLcmLarge 5 {2, 3, 5} ∧ ∑ a ∈ ({2, 3, 5} : Finset ℕ), (1 : ℚ) / a = 31 / 30 :=
  erdos_542_examples_closed.1
