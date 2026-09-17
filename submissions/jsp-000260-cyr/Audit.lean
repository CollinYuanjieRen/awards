import Proof

open Erdos311

#print axioms Erdos311.one_div_lcm_le_delta
#print axioms Erdos311.one_div_lcm_le_abs
#print axioms Erdos311.delta_le
#print axioms Erdos311.exists_delta_eq
#print axioms Erdos311.delta_pos
#print axioms Erdos311.lcmUpTo_pos

example : ∀ N : ℕ, 1 / (lcmUpTo N : ℚ) ≤ delta N := Erdos311.one_div_lcm_le_delta
example : ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N → 1 - unitSum A ≠ 0 →
    1 / (lcmUpTo N : ℚ) ≤ |1 - unitSum A| := Erdos311.one_div_lcm_le_abs
example : ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N → 1 - unitSum A ≠ 0 →
    delta N ≤ |1 - unitSum A| := Erdos311.delta_le
example : ∀ N : ℕ, ∃ A ⊆ Finset.Icc 1 N, 1 - unitSum A ≠ 0 ∧ delta N = |1 - unitSum A| :=
  Erdos311.exists_delta_eq
example : ∀ N : ℕ, 0 < delta N := Erdos311.delta_pos
example : ∀ N : ℕ, 0 < lcmUpTo N := Erdos311.lcmUpTo_pos

#print Erdos311.unitSum
#print Erdos311.lcmUpTo
#print Erdos311.deviations
#print Erdos311.delta
