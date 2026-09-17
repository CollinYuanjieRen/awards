/-
Comparator-style challenge module for JSP-000557 / Erdős Problem #685 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there. Every object is Mathlib's (`Nat.choose`, `Nat.primeFactors`, `Nat.factorization`,
`Real.log`); nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos685Challenge

theorem choose_le_pow_card_primeFactors (n k : ℕ) :
    n.choose k ≤ n ^ (n.choose k).primeFactors.card := by
  sorry

theorem log_choose_le_card_mul_log (n k : ℕ) :
    Real.log (n.choose k) ≤ ((n.choose k).primeFactors.card : ℝ) * Real.log n := by
  sorry

theorem log_choose_div_log_le_card (n k : ℕ) (hn : 2 ≤ n) :
    Real.log (n.choose k) / Real.log n ≤ ((n.choose k).primeFactors.card : ℝ) := by
  sorry

theorem strict_fails_two_one :
    Real.log (Nat.choose 2 1) / Real.log 2 = ((Nat.choose 2 1).primeFactors.card : ℝ) := by
  sorry

theorem pow_factorization_choose_le' (n k p : ℕ) (hn : 0 < n) :
    p ^ (n.choose k).factorization p ≤ n := by
  sorry

end Erdos685Challenge
