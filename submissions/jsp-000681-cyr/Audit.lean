import Erdos825NecessaryCond

open scoped ArithmeticFunction.sigma

#print axioms erdos_825_necessary_cond_closed
#print axioms Erdos825.erdos_825.variants.necessary_cond
#print axioms Erdos825.seventy_witness

/-- Erdős #825: any admissible constant exceeds 2. -/
example (C : ℝ) (hC : 0 < C)
    (h : ∀ (n : ℕ) (_ : σ 1 n > C * n), ∃ s ⊆ n.properDivisors, n = s.sum id) : 2 < C :=
  Erdos825.erdos_825.variants.necessary_cond C hC h
