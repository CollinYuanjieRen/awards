import Erdos744OddCycles

open Erdos744

#print axioms erdos_744_f_three_closed
#print axioms Erdos744.erdos_744_f_three

/-- Erdős #744: odd cycles show `f_3(n) = 1`. -/
example (n : ℕ) (h3 : 3 ≤ n) (hodd : Odd n) : f 3 n = 1 := (erdos_744_f_three n h3 hodd).2
