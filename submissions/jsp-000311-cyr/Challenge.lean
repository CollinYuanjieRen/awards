import Mathlib
/-! Mathlib-only comparator for JSP-000311 (central binomial coprime to 105). NOT imported by the build. -/
namespace CentralBinom105Challenge

theorem centralBinom_ten_coprime_105 : Nat.Coprime (Nat.centralBinom 10) 105 := by sorry

theorem exists_centralBinom_coprime_105 : ∃ n, 0 < n ∧ Nat.Coprime (Nat.centralBinom n) 105 := by sorry

end CentralBinom105Challenge
