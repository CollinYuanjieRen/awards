import Erdos1207IsoscelesFree

open Erdos1207

#print axioms erdos_1207_f_le_P
#print axioms erdos_1207_f_le_P_closed

/-- Erdős #1207: `f_d(n) ≤ P_d(n)` for all `d`, `n`. -/
example (d n : ℕ) : f d n ≤ P d n := erdos_1207_f_le_P d n
