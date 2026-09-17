import Erdos69TaoIdentity

open scoped ArithmeticFunction.omega

#print axioms erdos_69_tao_identity
#print axioms Erdos69.erdos_69.variants.specialisation_of_erdos_257

/-- Erdős #69: Tao's identity in the formal-conjectures shape
`erdos_69.variants.specialisation_of_erdos_257`. -/
example :
    let A := { n : ℕ | n.Prime }
    ∑' n, ω (n + 2) / (2 ^ (n + 2) : ℝ) = ∑' p : A, 1 / (2 ^ p.1 - 1) :=
  Erdos69.erdos_69.variants.specialisation_of_erdos_257

/-- `ω` is Mathlib's `ArithmeticFunction.cardDistinctFactors`. -/
example (n : ℕ) : ω n = ArithmeticFunction.cardDistinctFactors n := rfl
