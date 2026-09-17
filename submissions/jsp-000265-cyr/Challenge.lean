import Mathlib
/-! Mathlib-only comparator for JSP-000265 (minimal zero-sum signed reciprocals). NOT imported by the build. -/
namespace ZeroSumChallenge

def V : Finset ℚ := {1/2, -1/3, -1/6}

theorem V_sum : ∑ x ∈ V, x = 0 := by sorry

theorem V_minimal : ∀ T ∈ V.powerset, T.Nonempty → T ≠ V → ∑ x ∈ T, x ≠ 0 := by sorry

end ZeroSumChallenge
