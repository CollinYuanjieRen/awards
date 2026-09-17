/-
Comparator-style challenge module for JSP-000244 / Erdős Problem #287 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos287Challenge

/-- `l = [n₁, …, n_k]` is a representation of `1` by distinct unit fractions with denominators
`1 < n₁ < ⋯ < n_k`. -/
def UnitFractionRep (l : List ℕ) : Prop :=
  l.IsChain (· < ·) ∧ 1 < l.headI ∧ (l.map (fun n => (n : ℚ)⁻¹)).sum = 1

/-- The maximal consecutive gap `max (n_{i+1} − n_i)` of a list `[n₁, …, n_k]`. -/
def maxGap (l : List ℕ) : ℕ :=
  ((l.zip l.tail).map (fun p => p.2 - p.1)).foldr max 0

theorem not_forall_four_le_maxGap :
    ¬ ∀ l : List ℕ, UnitFractionRep l → 2 ≤ l.length → 4 ≤ maxGap l := by
  sorry

theorem unitFractionRep_example : UnitFractionRep [2, 3, 6] := by
  sorry

theorem maxGap_example : maxGap [2, 3, 6] = 3 := by
  sorry

theorem exists_unitFractionRep_maxGap_eq_three :
    ∃ l : List ℕ, UnitFractionRep l ∧ 2 ≤ l.length ∧ maxGap l = 3 := by
  sorry

end Erdos287Challenge
