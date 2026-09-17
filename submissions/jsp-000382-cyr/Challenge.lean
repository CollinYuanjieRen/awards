import Mathlib
/-! Mathlib-only comparator for JSP-000382 (weird numbers): 70 is weird. NOT imported by the build. -/
namespace WeirdChallenge

def IsWeird (n : ℕ) : Prop :=
  n < ∑ d ∈ n.properDivisors, d ∧
  ¬ ∃ S ∈ (n.properDivisors).powerset, ∑ d ∈ S, d = n

theorem seventy_isWeird : IsWeird 70 := by sorry

end WeirdChallenge
