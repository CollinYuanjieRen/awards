/-
Comparator-style challenge module for JSP-000260 / Erdős Problem #311 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos311Challenge

/-- `Σ_{n ∈ A} 1/n` in `ℚ`. -/
def unitSum (A : Finset ℕ) : ℚ := ∑ n ∈ A, (n : ℚ)⁻¹

/-- `[1, …, N]`, the least common multiple of `{1, …, N}`. -/
def lcmUpTo (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

/-- The non-zero values `|1 - Σ_{n ∈ A} 1/n|` over `A ⊆ {1, …, N}`. -/
def deviations (N : ℕ) : Finset ℚ :=
  ((Finset.Icc 1 N).powerset.image (fun A => |1 - unitSum A|)).filter (fun d => d ≠ 0)

theorem deviations_nonempty (N : ℕ) : (deviations N).Nonempty := by
  sorry

/-- `δ(N)`: the minimal non-zero value of `|1 - Σ_{n ∈ A} 1/n|`. -/
noncomputable def delta (N : ℕ) : ℚ := (deviations N).min' (deviations_nonempty N)

theorem one_div_lcm_le_delta (N : ℕ) : 1 / (lcmUpTo N : ℚ) ≤ delta N := by
  sorry

theorem one_div_lcm_le_abs (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (h : 1 - unitSum A ≠ 0) : 1 / (lcmUpTo N : ℚ) ≤ |1 - unitSum A| := by
  sorry

theorem delta_le (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (h : 1 - unitSum A ≠ 0) :
    delta N ≤ |1 - unitSum A| := by
  sorry

theorem exists_delta_eq (N : ℕ) :
    ∃ A ⊆ Finset.Icc 1 N, 1 - unitSum A ≠ 0 ∧ delta N = |1 - unitSum A| := by
  sorry

theorem delta_pos (N : ℕ) : 0 < delta N := by
  sorry

theorem lcmUpTo_pos (N : ℕ) : 0 < lcmUpTo N := by
  sorry

end Erdos311Challenge
