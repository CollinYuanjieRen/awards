import Mathlib

/-!
# Erdős Problem 295: definitions

A representation of `1` by distinct unit fractions with denominators at least `N` is a finite set
`D` of natural numbers, all `≥ N`, with `∑ d ∈ D, 1 / d = 1` (in `ℚ`).  Erdős's `k(N)` is the least
size of such a set (as an infimum in `ℕ`, it is `0` when no representation exists).
-/

namespace Erdos295

/-- `D` is a representation of `1` by distinct unit fractions with all denominators `≥ N`. -/
def IsUnitRepr (N : ℕ) (D : Finset ℕ) : Prop :=
  (∀ d ∈ D, N ≤ d) ∧ ∑ d ∈ D, (1 : ℚ) / d = 1

/-- Erdős's `k(N)`: the least number of distinct unit fractions with denominators `≥ N` summing
to `1`. -/
noncomputable def kmin (N : ℕ) : ℕ := sInf {m : ℕ | ∃ D : Finset ℕ, IsUnitRepr N D ∧ D.card = m}

/-- A representation of `1` is nonempty: the empty sum is `0 ≠ 1`. -/
theorem IsUnitRepr.nonempty {N : ℕ} {D : Finset ℕ} (h : IsUnitRepr N D) : D.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  simpa using h.2

/-- The real-valued sum of a representation is `1`. -/
theorem IsUnitRepr.sum_real {N : ℕ} {D : Finset ℕ} (h : IsUnitRepr N D) :
    ∑ d ∈ D, (1 : ℝ) / d = 1 := by
  have hq := congrArg (fun q : ℚ => (q : ℝ)) h.2
  push_cast at hq
  simpa using hq

end Erdos295
