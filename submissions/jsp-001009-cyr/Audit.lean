import Erdos1204Admissible

#print axioms erdos_1204_B_lt_A
#print axioms erdos_1204_B_lt_A_closed

/-- Erdős #1204: `B(k) < A(k)` for every `k ≥ 2`. -/
example (k : ℕ) (hk : 2 ≤ k) : (kB k : ℚ) / k < A k := erdos_1204_B_lt_A k hk
