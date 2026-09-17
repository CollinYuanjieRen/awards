import Proof

open Erdos287

#print axioms Erdos287.not_forall_four_le_maxGap
#print axioms Erdos287.unitFractionRep_example
#print axioms Erdos287.maxGap_example
#print axioms Erdos287.exists_unitFractionRep_maxGap_eq_three

example : ¬ ∀ l : List ℕ, UnitFractionRep l → 2 ≤ l.length → 4 ≤ maxGap l :=
  Erdos287.not_forall_four_le_maxGap
example : UnitFractionRep [2, 3, 6] := Erdos287.unitFractionRep_example
example : maxGap [2, 3, 6] = 3 := Erdos287.maxGap_example
example : ∃ l : List ℕ, UnitFractionRep l ∧ 2 ≤ l.length ∧ maxGap l = 3 :=
  Erdos287.exists_unitFractionRep_maxGap_eq_three

#print Erdos287.UnitFractionRep
#print Erdos287.maxGap
