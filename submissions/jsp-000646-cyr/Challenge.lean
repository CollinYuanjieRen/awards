import Mathlib
/-! Mathlib-only comparator for JSP-000646 (sum-avoiding subset). NOT imported by the build. -/
namespace SumAvoidingChallenge

theorem sum_avoiding (A : Finset ℕ) (hA : A.Nonempty) :
    ∀ x ∈ A.filter (fun a => A.max' hA < 2 * a),
    ∀ y ∈ A.filter (fun a => A.max' hA < 2 * a), x + y ∉ A := by sorry

end SumAvoidingChallenge
