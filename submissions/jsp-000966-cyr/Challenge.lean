import Mathlib

/-! Comparator-style challenge module (Mathlib-only; targets with `sorry`, not imported by the build)
for JSP-000966 / Erdős #1161: the (n−1)! lower bound on the maximal order-count in S_n. -/

namespace Challenge1161

open Equiv Nat

/-- `f n k` = number of elements of `S_n` of order `k`. -/
noncomputable def f (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun g : Perm (Fin n) => orderOf g = k)).card

theorem factorial_le_f (n : ℕ) (hn : 2 ≤ n) : (n - 1)! ≤ f n n := by
  sorry

theorem factorial_le_max (n : ℕ) (hn : 2 ≤ n) : ∃ k, (n - 1)! ≤ f n k := by
  sorry

end Challenge1161
