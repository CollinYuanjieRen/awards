import Mathlib
/-! Mathlib-only comparator for JSP-000991 (V_3(8)=0 no mono 3-AP). NOT imported by the build. -/
namespace MonoAPChallenge

def col (n : ℕ) : Bool := n == 2 || n == 4 || n == 5 || n == 7

theorem no_mono_3ap :
    ∀ a ∈ Finset.Icc 1 8, ∀ d ∈ Finset.Icc 1 8, a + 2 * d ≤ 8 →
      ¬ (col a = col (a + d) ∧ col (a + d) = col (a + 2 * d)) := by sorry

theorem exists_2col_no_mono_3ap :
    ∃ c : ℕ → Bool, ∀ a ∈ Finset.Icc 1 8, ∀ d ∈ Finset.Icc 1 8, a + 2 * d ≤ 8 →
      ¬ (c a = c (a + d) ∧ c (a + d) = c (a + 2 * d)) := by sorry

end MonoAPChallenge
