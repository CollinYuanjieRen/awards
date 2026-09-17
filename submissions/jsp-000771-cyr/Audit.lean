import Erdos929TrivialBound

#print axioms erdos_929_S_le
#print axioms erdos_929_S_le_closed

/-- Erdős #929: `S(k) ≤ k + 1`. -/
example (k : ℕ) : S k ≤ k + 1 := erdos_929_S_le k
