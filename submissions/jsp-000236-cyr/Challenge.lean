/-
Comparator-style challenge module for JSP-000236 / Erdős Problem #276 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
`Proof/Main.lean` (the definitions below are the ones of `Proof/Main.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos276Challenge

/-- A Lucas sequence: `a (n + 2) = a (n + 1) + a n` for all `n`. -/
def IsLucasSequence (a : ℕ → ℕ) : Prop := ∀ n, a (n + 2) = a (n + 1) + a n

/-- The pair `(a n, a (n + 1))` of the Lucas sequence with initial terms `x, y`. -/
def lucasPair (x y : ℕ) : ℕ → ℕ × ℕ
  | 0 => (x, y)
  | n + 1 => ((lucasPair x y n).2, (lucasPair x y n).1 + (lucasPair x y n).2)

/-- The Lucas sequence with initial terms `x, y`. -/
def lucas (x y : ℕ) (n : ℕ) : ℕ := (lucasPair x y n).1

/-- Vsemirnov's Lucas sequence: initial terms `106276436867, 35256392432`. -/
def vsemirnov : ℕ → ℕ := lucas 106276436867 35256392432

theorem exists_composite_lucasSequence :
    ∃ a : ℕ → ℕ, IsLucasSequence a ∧ (∀ k, 1 < a k ∧ ¬ (a k).Prime) ∧
      (∀ d, 2 ≤ d → ∃ k, ¬ d ∣ a k) := by
  sorry

theorem vsemirnov_exists_proper_factor : ∀ k, ∃ p, 1 < p ∧ p < vsemirnov k ∧ p ∣ vsemirnov k := by
  sorry

theorem vsemirnov_coprime_succ : ∀ k, Nat.Coprime (vsemirnov k) (vsemirnov (k + 1)) := by
  sorry

end Erdos276Challenge
