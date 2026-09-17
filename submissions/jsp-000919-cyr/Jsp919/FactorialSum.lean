import Mathlib

namespace FactorialPower

theorem factorial_sum_eq : Nat.factorial 1 + Nat.factorial 2 + Nat.factorial 3 = 9 := by
  decide

theorem factorial_sum_perfect_square :
    Nat.factorial 1 + Nat.factorial 2 + Nat.factorial 3 = 3 ^ 2 := by
  decide

theorem exists_factorial_sum_perfect_power :
    ∃ (a b c m k : ℕ), a < b ∧ b < c ∧ 2 ≤ k ∧
      Nat.factorial a + Nat.factorial b + Nat.factorial c = m ^ k := by
  refine ⟨1, 2, 3, 3, 2, ?_, ?_, ?_, ?_⟩ <;> decide

#print axioms FactorialPower.factorial_sum_perfect_square
#print axioms FactorialPower.exists_factorial_sum_perfect_power

end FactorialPower
