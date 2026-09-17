import Erdos242FourFractions

#print axioms erdos_242_four_unit_fractions
#print axioms erdos_242_four_unit_fractions_succ

/-- Erdős #242: for every `n > 2`, `4/n` is a sum of at most four distinct unit fractions. -/
example (n : ℕ) (hn : 2 < n) :
    ∃ S : Finset ℕ, (∀ s ∈ S, 0 < s) ∧ S.card ≤ 4 ∧ (4 / n : ℚ) = ∑ s ∈ S, (1 : ℚ) / s :=
  erdos_242_four_unit_fractions n hn
