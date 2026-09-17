import Mathlib
/-! Mathlib-only comparator for JSP-000919 (factorial-sum perfect power). NOT imported by the build. -/
namespace FactorialPowerChallenge

theorem factorial_sum_perfect_square :
    Nat.factorial 1 + Nat.factorial 2 + Nat.factorial 3 = 3 ^ 2 := by sorry

theorem exists_factorial_sum_perfect_power :
    ∃ (a b c m k : ℕ), a < b ∧ b < c ∧ 2 ≤ k ∧
      Nat.factorial a + Nat.factorial b + Nat.factorial c = m ^ k := by sorry

end FactorialPowerChallenge
