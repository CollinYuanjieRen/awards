import Mathlib

/-! Comparator-style challenge module (Mathlib-only definitions, targets with `sorry`; not imported by
the build) for JSP-000357 / Erdős #438, Massias's 11/32 square-sum-free construction. -/

namespace Challenge438

def R : Finset ℕ := {1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30}

def A (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun x => x % 32 ∈ R)

/-- Massias's construction is square-sum-free and attains density 11/32 along `N = 32 q`. -/
theorem massias_square_sum_free (q : ℕ) :
    (∀ a ∈ A (32 * q), ∀ b ∈ A (32 * q), ¬ IsSquare (a + b)) ∧ (A (32 * q)).card = 11 * q := by
  sorry

end Challenge438
