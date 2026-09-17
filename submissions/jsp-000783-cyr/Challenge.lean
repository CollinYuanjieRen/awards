import Mathlib
/-! Mathlib-only comparator for JSP-000783 (powerful numbers between squares). NOT imported by the build. -/
namespace PowerfulSquaresChallenge

def Powerful (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p

theorem powerful_pair_between_squares :
    Powerful 27 ∧ Powerful 32 ∧ 5 ^ 2 < 27 ∧ 27 < 32 ∧ 32 < 6 ^ 2 := by sorry

end PowerfulSquaresChallenge
