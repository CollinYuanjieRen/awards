import Mathlib
/-! Mathlib-only comparator for JSP-000882 (no element divides two others). NOT imported by the build. -/
namespace NoDivTwoChallenge

def A (n : ℕ) : Finset ℕ := Finset.Icc (n / 3 + 1) n

theorem A_card (n : ℕ) : (A n).card = n - n / 3 := by sorry

theorem A_no_two_multiples (n : ℕ) :
    ∀ a ∈ A n, ∀ b ∈ A n, ∀ c ∈ A n, b ≠ c → a ∣ b → a ∣ c → a = b ∨ a = c := by sorry

theorem exists_large_no_div_two (n : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 n ∧ B.card = n - n / 3 ∧
      (∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, b ≠ c → a ∣ b → a ∣ c → a = b ∨ a = c) := by sorry

end NoDivTwoChallenge
