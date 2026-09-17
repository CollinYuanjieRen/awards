import Erdos251Telescoping

#print axioms erdos_251_example_hasSum
#print axioms erdos_251_example_not_irrational
#print axioms erdos_251_example_closed

/-- Erdős #251: with `g_n = p_n + 1` the series `∑ p_n / (g_1 ⋯ g_n)` sums to `1`. -/
example : HasSum (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) /
    ∏ i ∈ Finset.range (n + 1), ((Nat.nth Nat.Prime i : ℝ) + 1)) 1 := erdos_251_example_closed.1
