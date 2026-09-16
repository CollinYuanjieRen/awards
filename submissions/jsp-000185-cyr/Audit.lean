import Proof

open Erdos196

#print axioms Erdos196.exists_monotoneAP3
#print axioms Erdos196.exists_increasingAP3

example : ∀ x : ℕ ≃ ℕ, ∃ i j k : ℕ, i < j ∧ j < k ∧ x i + x k = 2 * x j :=
  Erdos196.exists_monotoneAP3

example : ∀ x : ℕ ≃ ℕ, ∃ i j k : ℕ, i < j ∧ j < k ∧ x i < x j ∧ x j < x k ∧ x i + x k = 2 * x j :=
  Erdos196.exists_increasingAP3

#print Erdos196.HasMonotoneAP3
#print Erdos196.HasIncreasingAP3
