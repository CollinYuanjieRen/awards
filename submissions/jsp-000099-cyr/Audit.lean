import Proof

open Erdos82

#print axioms Erdos82.log_le_regGuarantee
#print axioms Erdos82.regThreshold_le_four_pow
#print axioms Erdos82.regThreshold_le_ramsey
#print axioms Erdos82.ramsey_le_choose
#print axioms Erdos82.regThreshold_three
#print axioms Erdos82.regGuarantee_five

example : ∀ m : ℕ, Nat.log 4 m ≤ regGuarantee m := Erdos82.log_le_regGuarantee
example : ∀ n : ℕ, regThreshold n ≤ 4 ^ n := Erdos82.regThreshold_le_four_pow
example : ∀ n : ℕ, regThreshold n ≤ ramsey n n := Erdos82.regThreshold_le_ramsey
example : ∀ m n : ℕ, ramsey m n ≤ (m + n).choose m - 1 := Erdos82.ramsey_le_choose
example : regThreshold 3 = 5 := Erdos82.regThreshold_three
example : regGuarantee 5 = 3 := Erdos82.regGuarantee_five

#print Erdos82.IsRegularOn
#print Erdos82.HasRegularInduced
#print Erdos82.RegProp
#print Erdos82.regThreshold
#print Erdos82.regGuarantee
#print Erdos82.ramsey
