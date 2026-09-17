import Erdos854GapsEven

#print axioms erdos_854_gap_even
#print axioms erdos_854_gap_even_closed

/-- Erdős #854: all gaps between consecutive integers coprime to the `k`-th primorial are even. -/
example (k i : ℕ) (hk : 1 ≤ k) : Even (coprimeSeq k (i + 1) - coprimeSeq k i) :=
  erdos_854_gap_even k i hk
