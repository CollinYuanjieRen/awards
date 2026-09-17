import Erdos394LowerBound

open Nat Filter Finset
open scoped Asymptotics

#print axioms erdos_394_lower_bound
#print axioms t_two_prime

/-- Erdős #394, the trivial lower bound, in the formal-conjectures shape
`erdos_394.variants.lower_bound` (`≪` unfolded to `IsBigO atTop` on `ℕ → ℝ`). -/
example : Asymptotics.IsBigO Filter.atTop ((fun x ↦ x ^ 2 / Real.log x) : ℕ → ℝ)
    ((fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) : ℕ → ℝ) := erdos_394_lower_bound

/-- The definition is the formal-conjectures one. -/
example (k n : ℕ) : t k n = sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) } := rfl
