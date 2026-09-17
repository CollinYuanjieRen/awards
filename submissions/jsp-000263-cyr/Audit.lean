import Proof

open Erdos317

#print axioms Erdos317.not_exists_small_signedSum
#print axioms Erdos317.one_div_lcm_le_abs_signedSum
#print axioms Erdos317.one_div_lcm_le_abs_fin
#print axioms Erdos317.exists_signedSum_eq_one_div_lcm
#print axioms Erdos317.lcmUpTo_pos

example : ∀ n : ℕ, ¬ ∃ δ : ℕ → ℚ, IsSign δ ∧ signedSum n δ ≠ 0 ∧ |signedSum n δ| < 1 / (lcmUpTo n : ℚ) :=
  Erdos317.not_exists_small_signedSum
example : ∀ (n : ℕ) (δ : ℕ → ℚ), IsSign δ → signedSum n δ ≠ 0 → 1 / (lcmUpTo n : ℚ) ≤ |signedSum n δ| :=
  Erdos317.one_div_lcm_le_abs_signedSum
example : ∀ (n : ℕ) (δ : Fin n → ℚ), (∀ k, δ k ∈ ({-1, 0, 1} : Set ℚ)) →
    ∑ k, δ k / (((k : ℕ) : ℚ) + 1) ≠ 0 →
    1 / (((Finset.Icc 1 n).lcm id : ℕ) : ℚ) ≤ |∑ k, δ k / (((k : ℕ) : ℚ) + 1)| :=
  Erdos317.one_div_lcm_le_abs_fin
example : ∃ δ : ℕ → ℚ, IsSign δ ∧ signedSum 4 δ ≠ 0 ∧ |signedSum 4 δ| = 1 / (lcmUpTo 4 : ℚ) :=
  Erdos317.exists_signedSum_eq_one_div_lcm
example : ∀ n : ℕ, 0 < lcmUpTo n := Erdos317.lcmUpTo_pos

#print Erdos317.IsSign
#print Erdos317.signedSum
#print Erdos317.lcmUpTo
