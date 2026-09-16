import Proof

open Erdos436 Filter

#print axioms Erdos436.lambda22_eq_nine
#print axioms Erdos436.runStart_le_nine
#print axioms Erdos436.exists_prime_gt_runStart_eq_nine

example : Lambda22 = 9 := Erdos436.lambda22_eq_nine

example : ∀ (p : ℕ) [Fact p.Prime], 11 ≤ p → runStart p ≤ 9 :=
  fun p _ hp => Erdos436.runStart_le_nine p hp

example : ∀ N : ℕ, ∃ p > N, p.Prime ∧ runStart p = 9 := Erdos436.exists_prime_gt_runStart_eq_nine

#print Erdos436.IsQR
#print Erdos436.IsRunStart
#print Erdos436.runStart
#print Erdos436.Lambda22
