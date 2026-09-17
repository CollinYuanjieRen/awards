/-
Comparator-style challenge module for JSP-000300 / Erdős Problem #364 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definition below is the one of `Proof/Main.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos364Challenge

/-- `n` is powerful: every prime dividing `n` divides it at least twice. -/
def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

theorem exists_consecutive_powerful_gt (N : ℕ) : ∃ n : ℕ, N < n ∧ Powerful n ∧ Powerful (n + 1) := by
  sorry

theorem infinite_consecutive_powerful : {n : ℕ | Powerful n ∧ Powerful (n + 1)}.Infinite := by
  sorry

theorem exists_pell_gt (N : ℕ) : ∃ x y : ℕ, N < y ∧ x ^ 2 = 8 * y ^ 2 + 1 := by
  sorry

theorem powerful_eight_mul_sq (y : ℕ) : Powerful (8 * y ^ 2) := by
  sorry

theorem powerful_sq (x : ℕ) : Powerful (x ^ 2) := by
  sorry

theorem not_four_consecutive_powerful (n : ℕ) :
    ¬ (Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) ∧ Powerful (n + 3)) := by
  sorry

end Erdos364Challenge
