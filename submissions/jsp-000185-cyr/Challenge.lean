/-
Comparator-style challenge module for JSP-000185 / Erdős Problem #196 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
`Proof/Main.lean` (the definitions below are the ones of `Proof/Main.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos196Challenge

/-- `x` has a monotone 3-term arithmetic progression: indices `i < j < k` whose values are in
arithmetic progression (`x i + x k = 2 x j`, increasing or decreasing). -/
def HasMonotoneAP3 (x : ℕ ≃ ℕ) : Prop := ∃ i j k : ℕ, i < j ∧ j < k ∧ x i + x k = 2 * x j

/-- The progression found in the proof is increasing: `x i < x j < x k`. -/
def HasIncreasingAP3 (x : ℕ ≃ ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧ x i < x j ∧ x j < x k ∧ x i + x k = 2 * x j

theorem exists_monotoneAP3 (x : ℕ ≃ ℕ) : HasMonotoneAP3 x := by
  sorry

theorem exists_increasingAP3 (x : ℕ ≃ ℕ) : HasIncreasingAP3 x := by
  sorry

end Erdos196Challenge
