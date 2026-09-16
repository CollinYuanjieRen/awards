import Mathlib

/-! Comparator-style challenge module (Mathlib-only definitions, target with `sorry`; not
imported by the build) for JSP-000703 / Erdős #850, two-consecutive component. -/

namespace Challenge850

def TwoConsecutiveExample (x y : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ x ≠ y ∧ x.primeFactors = y.primeFactors ∧
    (x + 1).primeFactors = (y + 1).primeFactors

theorem erdos_family (r : ℕ) (hr : 1 ≤ r) :
    TwoConsecutiveExample (2 * (2 ^ r - 1)) (2 * (2 ^ r - 1) * (2 * (2 ^ r - 1) + 2)) := by
  sorry

theorem makowski_example : TwoConsecutiveExample 75 1215 := by
  sorry

end Challenge850
