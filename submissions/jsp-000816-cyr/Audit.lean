import Erdos983TrivialBound

#print axioms erdos_983_f_le_primeCounting
#print axioms erdos_983_f_le_primeCounting_closed

/-- Erdős #983: `f(k, n) ≤ π(n)` whenever `π(n) < k`. -/
example (k n : ℕ) (hk : Nat.primeCounting n < k) : f k n ≤ Nat.primeCounting n :=
  erdos_983_f_le_primeCounting k n hk
