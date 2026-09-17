import Proof

open Erdos1029

#print axioms Erdos1029.mul_two_pow_half_le
#print axioms Erdos1029.two_pow_lt_R_sq
#print axioms Erdos1029.ramsey_le_choose_sharp
#print axioms Erdos1029.R_le_choose_page
#print axioms Erdos1029.lt_R_of_count

example : ∀ k : ℕ, (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 2 * Real.sqrt 2 * Real.exp 1 * ((R k : ℝ) + 1) :=
  Erdos1029.mul_two_pow_half_le
example : ∀ k : ℕ, 3 ≤ k → 2 ^ k < R k ^ 2 := Erdos1029.two_pow_lt_R_sq
example : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ramsey m n ≤ (m + n - 2).choose (m - 1) :=
  Erdos1029.ramsey_le_choose_sharp
example : ∀ k : ℕ, 1 ≤ k → R k ≤ (2 * k - 1).choose (k - 1) := Erdos1029.R_le_choose_page
example : ∀ k N : ℕ, k ≤ N → N.choose k * 2 * 2 ^ (N.choose 2 - k.choose 2) < 2 ^ (N.choose 2) → N < R k :=
  Erdos1029.lt_R_of_count

#print Erdos1029.IsGood
#print Erdos1029.RamseyProp
#print Erdos1029.ramsey
#print Erdos1029.R
