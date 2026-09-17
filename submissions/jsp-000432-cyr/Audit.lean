import Erdos539SqrtLower

open Filter
open scoped Asymptotics Finset

#print axioms erdos_539_sq_isBigO
#print axioms ceil_sqrt_le_cofactorThreshold
#print axioms isCofactorLowerBound_ceil_sqrt

/-- Erdős #539, the Erdős–Szemerédi lower bound, in the formal-conjectures shape
`erdos_539.variants.sq_isBigO`. -/
example : (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (cofactorThreshold n : ℝ) := erdos_539_sq_isBigO

/-- The explicit bound behind it. -/
example (n : ℕ) : ⌈Real.sqrt n⌉₊ ≤ cofactorThreshold n := ceil_sqrt_le_cofactorThreshold n

/-- The definitions are the formal-conjectures ones. -/
example (n : ℕ) : cofactorThreshold n = sSup {m | IsCofactorLowerBound n m} := rfl
