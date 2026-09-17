import Mathlib
/-! Mathlib-only comparator for JSP-000647 (sums avoid a prescribed set). NOT imported by the build. -/
namespace SumsAvoidBChallenge

theorem sums_avoid (A B : Finset ℕ) (hB : B.Nonempty) :
    ∀ x ∈ A.filter (fun a => B.max' hB < 2 * a),
    ∀ y ∈ A.filter (fun a => B.max' hB < 2 * a), x + y ∉ B := by sorry

end SumsAvoidBChallenge
