import JSP518

#print axioms JKLY.jkly_distinct_degrees_nat
#print axioms JKLY.jkly_distinct_degrees
#print axioms JKLY.jkly_theorem2
#print axioms JKLY.lemma7
#print axioms JKLY.lemma4
#print axioms JKLY.antic_bound
#print axioms JKLY.exists_diverse_subgraph_of_ramseyFree
#print axioms JKLY.exists_indepSet_subset_card_ge_of_edges
#print axioms JKLY.PB.chebyshev_sq_bound
#print axioms JKLY.card_filter_shift_le
#print axioms Erdos637.erdos_637
#print axioms Erdos88.ksssLemma44

example (k : ℕ) : ∃ β : ℝ, 0 < β ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree ((k : ℝ) + 1) G →
      ∃ W : Finset (Fin n),
        β * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ Erdos637.numDistinctDegrees G W :=
  JKLY.jkly_distinct_degrees_nat k

example (C : ℝ) (hC : 0 < C) : ∃ β : ℝ, 0 < β ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
      ∃ W : Finset (Fin n), β * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ Erdos637.numDistinctDegrees G W :=
  JKLY.jkly_distinct_degrees C hC
