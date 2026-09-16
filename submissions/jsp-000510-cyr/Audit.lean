import Proof

open Erdos629

#print axioms Erdos629.two_pow_le_listThreshold
#print axioms Erdos629.ert_lower_bound
#print axioms Erdos629.listThreshold_le
#print axioms Erdos629.listThreshold_one

example : ∀ k, 2 ^ k ≤ listThreshold k := fun k => Erdos629.two_pow_le_listThreshold k
example : ∀ k, 1 ≤ k → 2 ^ (k - 1) < listThreshold k := Erdos629.ert_lower_bound
example : ∀ k, listThreshold k ≤ 2 * (2 * k - 1).choose k := Erdos629.listThreshold_le
example : listThreshold 1 = 2 := Erdos629.listThreshold_one

#print Erdos629.ListColorable
#print Erdos629.Choosable
#print Erdos629.listThreshold
