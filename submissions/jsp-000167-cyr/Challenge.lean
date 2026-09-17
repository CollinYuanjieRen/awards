import Mathlib
/-! Mathlib-only comparator for JSP-000167 (sparse ruler). NOT imported by the build. -/
namespace SparseRulerChallenge

def Measures (S : Finset ℕ) (L : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 L, ∃ a ∈ S, ∃ b ∈ S, b < a ∧ a - b = k

theorem card_choose_two_ge {S : Finset ℕ} {L : ℕ} (h : Measures S L) :
    L ≤ S.card.choose 2 := by sorry

theorem perfect_ruler_0146 : Measures ({0, 1, 4, 6} : Finset ℕ) 6 := by sorry

end SparseRulerChallenge
