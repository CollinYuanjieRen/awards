import Proof

open Erdos77

#print axioms Erdos77.sqrt_two_le_liminf
#print axioms Erdos77.limsup_le_four
#print axioms Erdos77.sqrt_two_le_R_rpow
#print axioms Erdos77.R_rpow_le_four

example : Real.sqrt 2 ≤ Filter.liminf (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop :=
  Erdos77.sqrt_two_le_liminf
example : Filter.limsup (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop ≤ 4 :=
  Erdos77.limsup_le_four
example : ∀ k : ℕ, 3 ≤ k → Real.sqrt 2 ≤ (R k : ℝ) ^ (1 / (k : ℝ)) := Erdos77.sqrt_two_le_R_rpow
example : ∀ k : ℕ, 1 ≤ k → (R k : ℝ) ^ (1 / (k : ℝ)) ≤ 4 := Erdos77.R_rpow_le_four

#print Erdos77.IsGood
#print Erdos77.RamseyProp
#print Erdos77.ramsey
#print Erdos77.R
