import Mathlib
/-! Mathlib-only comparator for JSP-000915 (squarefree pairwise sums). NOT imported by the build. -/
namespace SquarefreeSumsChallenge

def S : Finset ℕ := {1, 2, 4, 9, 13}

theorem S_pairwise_sum_squarefree :
    ∀ a ∈ S, ∀ b ∈ S, a < b → Squarefree (a + b) := by sorry

theorem exists_squarefree_sum_set :
    ∃ T : Finset ℕ, T.card = 5 ∧ ∀ a ∈ T, ∀ b ∈ T, a < b → Squarefree (a + b) := by sorry

end SquarefreeSumsChallenge
