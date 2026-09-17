import Erdos367PowerfulParts

open Filter Finset
open scoped Asymptotics

#print axioms erdos_367_k_le_two
#print axioms erdos_367_two
#print axioms B_dvd

/-- Erdős #367, the trivial `k ≤ 2` bound, in the formal-conjectures shape
`erdos_367.variants.k_le_two`. -/
example : ∀ k : ℕ, k ≤ 2 →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := erdos_367_k_le_two

/-- The definition is the formal-conjectures one. -/
example (r n : ℕ) : B r n = ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i := rfl
