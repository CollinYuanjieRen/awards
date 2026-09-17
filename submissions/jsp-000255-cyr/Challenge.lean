import Mathlib
/-! Mathlib-only comparator for JSP-000255 (distinct unit fractions). NOT imported by the build. -/
namespace UnitFractionsChallenge

theorem four_fifths_eq : (1:ℚ)/2 + 1/4 + 1/20 = 4/5 := by sorry

theorem exists_three_distinct_unit_fractions :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ (1:ℚ)/a + 1/b + 1/c = 4/5 := by sorry

end UnitFractionsChallenge
