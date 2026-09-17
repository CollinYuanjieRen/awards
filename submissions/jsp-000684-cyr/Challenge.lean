/-
Comparator-style challenge module for JSP-000684 / Erdős Problem #828 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there. Every object is Mathlib's (`Nat.totient`, divisibility); nothing in this file is used
by the proof.
-/
import Mathlib

namespace Erdos828Challenge

theorem totient_dvd_iff (n : ℕ) :
    Nat.totient n ∣ n ↔ n ≤ 1 ∨ ∃ a b : ℕ, 0 < a ∧ n = 2 ^ a * 3 ^ b := by
  sorry

theorem totient_dvd_two_pow_mul_three_pow (a b : ℕ) (ha : 0 < a) :
    Nat.totient (2 ^ a * 3 ^ b) ∣ 2 ^ a * 3 ^ b := by
  sorry

theorem exists_eq_two_pow_mul_three_pow_of_totient_dvd (n : ℕ) (hn : 2 ≤ n)
    (h : Nat.totient n ∣ n) : ∃ a b : ℕ, 0 < a ∧ n = 2 ^ a * 3 ^ b := by
  sorry

theorem not_totient_dvd_three_pow (b : ℕ) (hb : 0 < b) : ¬ Nat.totient (3 ^ b) ∣ 3 ^ b := by
  sorry

end Erdos828Challenge
