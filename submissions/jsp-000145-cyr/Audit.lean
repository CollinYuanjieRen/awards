import Erdos143Primitive

open Erdos143

#print axioms erdos_143_primitive_closed
#print axioms Erdos143.isPrimitive_of_wellSeparated

/-- Erdős #143: the natural numbers in a well-separated set form a primitive set. -/
example {A : Set ℝ} (hA : WellSeparatedSet A) : IsPrimitive {n : ℕ | (n : ℝ) ∈ A} :=
  isPrimitive_of_wellSeparated hA
