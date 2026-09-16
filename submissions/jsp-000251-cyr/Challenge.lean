/-
Comparator-style challenge module for JSP-000251 / Erdős Problem #295 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
`Proof/Main.lean` (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos295Challenge

/-- `D` is a representation of `1` by distinct unit fractions with all denominators `≥ N`. -/
def IsUnitRepr (N : ℕ) (D : Finset ℕ) : Prop :=
  (∀ d ∈ D, N ≤ d) ∧ ∑ d ∈ D, (1 : ℚ) / d = 1

/-- Erdős's `k(N)`: the least number of distinct unit fractions with denominators `≥ N` summing
to `1`. -/
noncomputable def kmin (N : ℕ) : ℕ := sInf {m : ℕ | ∃ D : Finset ℕ, IsUnitRepr N D ∧ D.card = m}

theorem card_ge_of_isUnitRepr (N : ℕ) (D : Finset ℕ) (hD : IsUnitRepr N D) :
    (Real.exp 1 - 1) * ((N : ℝ) - 1) ≤ D.card := by
  sorry

theorem le_kmin (N : ℕ) (h : ∃ D : Finset ℕ, IsUnitRepr N D) :
    (Real.exp 1 - 1) * ((N : ℝ) - 1) ≤ kmin N := by
  sorry

end Erdos295Challenge
