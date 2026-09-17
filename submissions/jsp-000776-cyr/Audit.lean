import Erdos934HOne

open Erdos934

#print axioms erdos_934_h_one_closed
#print axioms Erdos934.erdos_934_h_one

/-- Erdős #934: `h_1(d) = d + 1` for `d ≥ 3`. -/
example (d : ℕ) (hd : 3 ≤ d) : h₁ d = d + 1 := (erdos_934_h_one d hd).2
