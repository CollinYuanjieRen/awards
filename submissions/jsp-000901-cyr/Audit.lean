import Proof

open Erdos1084

#print axioms Erdos1084.contactOne_eq
#print axioms Erdos1084.unitPairs_le_of_isSeparated
#print axioms Erdos1084.exists_isSeparated_unitPairs_eq

example : ∀ n : ℕ, contactOne n = n - 1 := Erdos1084.contactOne_eq

example : ∀ A : Finset ℝ, IsSeparated A → unitPairs A ≤ A.card - 1 :=
  Erdos1084.unitPairs_le_of_isSeparated

example : ∀ n : ℕ, ∃ A : Finset ℝ, A.card = n ∧ IsSeparated A ∧ unitPairs A = n - 1 :=
  Erdos1084.exists_isSeparated_unitPairs_eq

#print Erdos1084.IsSeparated
#print Erdos1084.unitPairs
#print Erdos1084.contactOne
