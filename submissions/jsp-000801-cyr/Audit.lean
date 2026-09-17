import Proof

open Erdos963

#print axioms Erdos963.log_three_le_f
#print axioms Erdos963.exists_dissociated_subset
#print axioms Erdos963.exists_dissociated_subset_log
#print axioms Erdos963.f_le
#print axioms Erdos963.exists_dissociated_subset_f

example : ∀ n : ℕ, Nat.log 3 n ≤ f n := Erdos963.log_three_le_f
example : ∀ A : Finset ℝ, ∃ B ⊆ A, Dissociated B ∧ A.card ≤ 3 ^ B.card :=
  Erdos963.exists_dissociated_subset
example : ∀ A : Finset ℝ, ∃ B ⊆ A, Dissociated B ∧ Nat.log 3 A.card ≤ B.card :=
  Erdos963.exists_dissociated_subset_log
example : ∀ n : ℕ, f n ≤ n := Erdos963.f_le
example : ∀ (n : ℕ) (A : Finset ℝ), A.card = n → ∃ B ⊆ A, Dissociated B ∧ f n ≤ B.card :=
  Erdos963.exists_dissociated_subset_f

#print Erdos963.Dissociated
#print Erdos963.f
