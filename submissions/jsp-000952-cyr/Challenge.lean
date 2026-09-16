/-
Comparator-style challenge module for JSP-000952 / Erdős Problem #1147.

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
`Proof/Main.lean` (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

open Filter

namespace Erdos1147Challenge

/-- Distance from `x` to the nearest integer. -/
noncomputable def nd (x : ℝ) : ℝ := |x - round x|

/-- Every sufficiently large natural number is a sum of two elements of `A`. -/
def IsAsymptoticBasis2 (A : Set ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ m : ℕ, n₀ ≤ m → ∃ a ∈ A, ∃ b ∈ A, a + b = m

/-- The recurrence set `{n ≥ 1 : ‖α n²‖ ≤ ε n}`. -/
def recSet (α : ℝ) (ε : ℕ → ℝ) : Set ℕ := {n | 1 ≤ n ∧ nd (α * (n : ℝ) ^ 2) ≤ ε n}

/-- The set displayed in Erdős Problem 1147: `{n ≥ 1 : ‖α n²‖ < 1 / log n}`. -/
def erdosSet (α : ℝ) : Set ℕ := {n | 1 ≤ n ∧ nd (α * (n : ℝ) ^ 2) < 1 / Real.log n}

theorem sqrtTwo_recSet_not_basis (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) :
    ¬ IsAsymptoticBasis2 (recSet (Real.sqrt 2) ε) := by
  sorry

theorem not_erdos_1147 :
    ¬ ∀ α : ℝ, 0 < α → Irrational α → IsAsymptoticBasis2 (erdosSet α) := by
  sorry

theorem not_erdos_1147_le :
    ¬ ∀ α : ℝ, 0 < α → Irrational α →
      IsAsymptoticBasis2 (recSet α (fun n => 1 / Real.log n)) := by
  sorry

end Erdos1147Challenge
