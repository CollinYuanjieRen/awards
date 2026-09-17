import Proof

open Erdos301

#print axioms Erdos301.half_le_f
#print axioms Erdos301.not_hasUnitSolution_upperHalf
#print axioms Erdos301.card_upperHalf
#print axioms Erdos301.exists_dvd_of_half_lt_card
#print axioms Erdos301.card_le_half_of_not_hasRepeatedUnitSolution
#print axioms Erdos301.not_hasRepeatedUnitSolution_upperHalf

example : ∀ N : ℕ, (N + 1) / 2 ≤ f N := Erdos301.half_le_f
example : ∀ N : ℕ, ¬ HasUnitSolution (upperHalf N) := Erdos301.not_hasUnitSolution_upperHalf
example : ∀ N : ℕ, (upperHalf N).card = (N + 1) / 2 := Erdos301.card_upperHalf
example : ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N → (N + 1) / 2 < A.card →
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a ∣ b := Erdos301.exists_dvd_of_half_lt_card
example : ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N → ¬ HasRepeatedUnitSolution A →
    A.card ≤ (N + 1) / 2 := Erdos301.card_le_half_of_not_hasRepeatedUnitSolution
example : ∀ N : ℕ, ¬ HasRepeatedUnitSolution (upperHalf N) :=
  Erdos301.not_hasRepeatedUnitSolution_upperHalf

#print Erdos301.HasUnitSolution
#print Erdos301.HasRepeatedUnitSolution
#print Erdos301.upperHalf
#print Erdos301.f
