import Mathlib

/-!
# `lcmUpTo`: the least common multiple `[1, …, N]`

This module fixes `lcmUpTo N = [1, …, N]`, the least common multiple of `{1, …, N}`, and the
two elementary facts about it that the main argument for Erdős problem #317 needs: it is
positive, and every element of `{1, …, N}` divides it.

Reused from our own JSP-000260 package (Erdős #311).
-/

namespace Erdos317

/-- `lcmUpTo N = [1, …, N]`, the least common multiple of `{1, …, N}`. -/
def lcmUpTo (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

/-- (T5) The least common multiple `[1, …, n]` is positive: no element of `{1, …, n}` is `0`. -/
theorem lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := by
  refine Nat.pos_of_ne_zero ?_
  show (Finset.Icc 1 n).lcm id ≠ 0
  refine Finset.lcm_ne_zero_iff.2 ?_
  intro x hx
  have h1 : 1 ≤ x := (Finset.mem_Icc.1 hx).1
  simp only [id_eq]
  omega

/-- Every element of `{1, …, N}` divides `lcmUpTo N`. -/
theorem dvd_lcmUpTo {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) : n ∣ lcmUpTo N :=
  Finset.dvd_lcm hn

end Erdos317
