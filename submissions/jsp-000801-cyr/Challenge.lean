/-
Comparator-style challenge module for JSP-000801 / Erdős Problem #963 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos963Challenge

/-- `B` is dissociated: all subset sums are distinct. -/
def Dissociated (B : Finset ℝ) : Prop := ∀ S ⊆ B, ∀ T ⊆ B, ∑ x ∈ S, x = ∑ x ∈ T, x → S = T

/-- `f n`: the largest `k` such that every `n`-element set of reals contains a dissociated subset
of size at least `k`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n → ∃ B ⊆ A, Dissociated B ∧ k ≤ B.card}

theorem log_three_le_f (n : ℕ) : Nat.log 3 n ≤ f n := by
  sorry

theorem exists_dissociated_subset (A : Finset ℝ) : ∃ B ⊆ A, Dissociated B ∧ A.card ≤ 3 ^ B.card := by
  sorry

theorem exists_dissociated_subset_log (A : Finset ℝ) :
    ∃ B ⊆ A, Dissociated B ∧ Nat.log 3 A.card ≤ B.card := by
  sorry

theorem f_le (n : ℕ) : f n ≤ n := by
  sorry

theorem exists_dissociated_subset_f (n : ℕ) (A : Finset ℝ) (hA : A.card = n) :
    ∃ B ⊆ A, Dissociated B ∧ f n ≤ B.card := by
  sorry

end Erdos963Challenge
