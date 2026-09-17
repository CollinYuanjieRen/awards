/-
Comparator-style challenge module for JSP-000263 / Erdős Problem #317 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Lcm.lean` and `Proof/Main.lean`,
repeated verbatim). Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos317Challenge

/-- `[1, …, N]`, the least common multiple of `{1, …, N}`. -/
def lcmUpTo (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

/-- Every `δ_k` lies in `{-1, 0, 1}`. -/
def IsSign (δ : ℕ → ℚ) : Prop := ∀ k, δ k = -1 ∨ δ k = 0 ∨ δ k = 1

/-- `Σ_{1 ≤ k ≤ n} δ_k / k`. -/
def signedSum (n : ℕ) (δ : ℕ → ℚ) : ℚ := ∑ k ∈ Finset.Icc 1 n, δ k / k

theorem not_exists_small_signedSum (n : ℕ) :
    ¬ ∃ δ : ℕ → ℚ, IsSign δ ∧ signedSum n δ ≠ 0 ∧ |signedSum n δ| < 1 / (lcmUpTo n : ℚ) := by
  sorry

theorem one_div_lcm_le_abs_signedSum (n : ℕ) (δ : ℕ → ℚ) (hδ : IsSign δ) (h : signedSum n δ ≠ 0) :
    1 / (lcmUpTo n : ℚ) ≤ |signedSum n δ| := by
  sorry

theorem one_div_lcm_le_abs_fin (n : ℕ) (δ : Fin n → ℚ) (hδ : ∀ k, δ k ∈ ({-1, 0, 1} : Set ℚ))
    (h : ∑ k, δ k / (((k : ℕ) : ℚ) + 1) ≠ 0) :
    1 / (((Finset.Icc 1 n).lcm id : ℕ) : ℚ) ≤ |∑ k, δ k / (((k : ℕ) : ℚ) + 1)| := by
  sorry

theorem exists_signedSum_eq_one_div_lcm :
    ∃ δ : ℕ → ℚ, IsSign δ ∧ signedSum 4 δ ≠ 0 ∧ |signedSum 4 δ| = 1 / (lcmUpTo 4 : ℚ) := by
  sorry

theorem lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := by
  sorry

end Erdos317Challenge
