import Erdos400LogBound

open Nat Filter Finset
open scoped Asymptotics Topology

#print axioms erdos_400_upper_bound
#print axioms g_isBigO_log
#print axioms g_le

/-- Erdős #400, the easy upper bound, in the formal-conjectures shape
`erdos_400.variants.upper_bound` (`≪` is `IsBigO atTop`). -/
example (k : ℕ) (hk : k ≥ 2) :
    (fun n : ℕ ↦ (g k n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) := erdos_400_upper_bound k hk

/-- The explicit bound behind it. -/
example (k n : ℕ) : g k n ≤ k * (Nat.log 2 n + 1) := g_le k n

/-- The definition is the formal-conjectures one. -/
example (k n : ℕ) : g k n = sSup { ((∑ i, a i) - n) | (a : Fin k → ℕ) (_ : (∏ i, (a i) !) ∣ n !) } := rfl
