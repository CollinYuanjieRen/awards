import Proof

open Erdos812

#print axioms Erdos812.R_succ_ge_all
#print axioms Erdos812.R_succ_sub_ge
#print axioms Erdos812.ramsey_succ_right
#print axioms Erdos812.ramseyProp_ramsey

example : ∀ n : ℕ, R n + (4 * n - 4) ≤ R (n + 1) := Erdos812.R_succ_ge_all
example : ∀ n : ℕ, 2 ≤ n → (R (n + 1) : ℤ) - (R n : ℤ) ≥ 4 * (n : ℤ) - 8 := Erdos812.R_succ_sub_ge
example : ∀ m n : ℕ, 2 ≤ m → 2 ≤ n → ramsey m n + (2 * m - 3) ≤ ramsey m (n + 1) :=
  Erdos812.ramsey_succ_right
example : ∀ m n : ℕ, RamseyProp (ramsey m n) m n := Erdos812.ramseyProp_ramsey

#print Erdos812.IsGood
#print Erdos812.RamseyProp
#print Erdos812.ramsey
#print Erdos812.R
