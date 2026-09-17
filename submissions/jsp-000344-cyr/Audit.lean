import Proof

open Erdos417

#print axioms Erdos417.V'_le_V
#print axioms Erdos417.totientValues_subset
#print axioms Erdos417.mem_totientValues
#print axioms Erdos417.mem_totientValuesLE
#print axioms Erdos417.V'_le_V_real

example : ∀ x : ℕ, V' x ≤ V x := Erdos417.V'_le_V
example : ∀ x : ℕ, totientValues x ⊆ totientValuesLE x := Erdos417.totientValues_subset
example : ∀ x v : ℕ, v ∈ totientValues x ↔ ∃ m, 1 ≤ m ∧ m ≤ x ∧ Nat.totient m = v :=
  Erdos417.mem_totientValues
example : ∀ x v : ℕ, v ∈ totientValuesLE x ↔ v ≤ x ∧ ∃ m, 1 ≤ m ∧ Nat.totient m = v :=
  Erdos417.mem_totientValuesLE
example : ∀ x : ℝ, V' ⌊x⌋₊ ≤ V ⌊x⌋₊ := Erdos417.V'_le_V_real

#print Erdos417.totientValues
#print Erdos417.totientValuesLE
#print Erdos417.V'
#print Erdos417.V
