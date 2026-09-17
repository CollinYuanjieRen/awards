import Mathlib
/-! Mathlib-only comparator for JSP-000430 (no three equal pairwise LCMs). NOT imported by the build. -/
namespace EqualLcmChallenge

def C : Finset ℕ := {1, 2, 4, 8, 16, 32}

theorem C_no_equal_lcm_triple :
    ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a < b → b < c →
      ¬ (Nat.lcm a b = Nat.lcm a c ∧ Nat.lcm a c = Nat.lcm b c) := by sorry

theorem bad_triple : Nat.lcm 6 10 = 30 ∧ Nat.lcm 6 15 = 30 ∧ Nat.lcm 10 15 = 30 := by sorry

end EqualLcmChallenge
