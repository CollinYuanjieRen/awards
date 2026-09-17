import Mathlib

namespace EqualLcm

def C : Finset ℕ := {1, 2, 4, 8, 16, 32}

/-- The chain has no three DISTINCT elements with all three pairwise LCMs equal. -/
theorem C_no_equal_lcm_triple :
    ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a < b → b < c →
      ¬ (Nat.lcm a b = Nat.lcm a c ∧ Nat.lcm a c = Nat.lcm b c) := by
  decide

/-- The forbidden configuration is realizable. -/
theorem bad_triple : Nat.lcm 6 10 = 30 ∧ Nat.lcm 6 15 = 30 ∧ Nat.lcm 10 15 = 30 := by
  decide

#print axioms EqualLcm.C_no_equal_lcm_triple
#print axioms EqualLcm.bad_triple

end EqualLcm
