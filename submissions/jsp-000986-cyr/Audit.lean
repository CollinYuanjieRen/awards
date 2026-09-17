import Erdos1181Primorial

#print axioms erdos_1181_primorial_dvd
#print axioms erdos_1181_primorial_le
#print axioms erdos_1181_primorial_le_closed

/-- Erdős #1181: the primorial of the primes below `q(n, k)` is at most `∏_{1 ≤ i ≤ k} (n + i)`. -/
example (n k : ℕ) : primorial (q n k - 1) ≤ intervalProd n k := erdos_1181_primorial_le n k
