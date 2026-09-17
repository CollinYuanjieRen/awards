import Proof

open Erdos1030

#print axioms Erdos1030.offdiag_sub_ge
#print axioms Erdos1030.offdiag_ge
#print axioms Erdos1030.offdiag_sub_ge_trivial

example : ∀ k : ℕ, (ramsey (k + 1) k : ℤ) - (R k : ℤ) ≥ 2 * (k : ℤ) - 5 := Erdos1030.offdiag_sub_ge
example : ∀ k : ℕ, 2 ≤ k → R k + (2 * k - 3) ≤ ramsey (k + 1) k := Erdos1030.offdiag_ge
example : ∀ k : ℕ, (ramsey (k + 1) k : ℤ) - (R k : ℤ) ≥ (k : ℤ) - 2 := Erdos1030.offdiag_sub_ge_trivial

#print Erdos1030.IsGood
#print Erdos1030.RamseyProp
#print Erdos1030.ramsey
#print Erdos1030.R
