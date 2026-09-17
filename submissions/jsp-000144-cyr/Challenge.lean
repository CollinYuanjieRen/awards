import Mathlib
/-! Mathlib-only comparator for JSP-000144 (r_3(14) >= 8 AP-free set). NOT imported by the build. -/
namespace APFreeChallenge

def S : Finset ℕ := {1, 2, 4, 5, 10, 11, 13, 14}

theorem S_ap_free : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + c = 2 * b → a = c := by sorry

theorem r3_14_ge_8 :
    ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 14 ∧ T.card = 8 ∧
      (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a + c = 2 * b → a = c) := by sorry

end APFreeChallenge
