import Mathlib
/-! Mathlib-only comparator for JSP-000634 (Sidon set among squares). NOT imported by the build. -/
namespace SidonSquaresChallenge

def S : Finset ℕ := {1, 4, 9, 16, 25, 36}

theorem S_sidon :
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + b = c + d → ({a, b} : Finset ℕ) = {c, d} := by sorry

theorem S_all_squares : ∀ x ∈ S, ∃ k, x = k ^ 2 := by sorry

end SidonSquaresChallenge
