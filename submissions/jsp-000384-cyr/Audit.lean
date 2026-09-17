import Erdos472Ulam

#print axioms erdos_472_example
#print axioms ulamNext_spec
#print axioms ulamNext_le

/-- Erdős #472: from `3, 5` Ulam's rule continues `7, 11, 13, 17`. -/
example : ulamExtend [3, 5] 4 = [3, 5, 7, 11, 13, 17] := erdos_472_example.2.2.2.2
