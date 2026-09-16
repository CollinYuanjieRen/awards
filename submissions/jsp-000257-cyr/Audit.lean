import Erdos306One

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

#print axioms erdos_306_one

/-- The instance `a/b = 1` of Erdős Problem #306, in the formal-conjectures shape. -/
example :
    ∃ k : ℕ, ∃ n : Fin (k + 1) → ℕ, n 0 = 1 ∧ StrictMono n ∧
      (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
      (1 : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) :=
  erdos_306_one
