import Mathlib

namespace SidonSquares

def S : Finset ℕ := {1, 4, 9, 16, 25, 36}

theorem S_sidon :
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + b = c + d → ({a, b} : Finset ℕ) = {c, d} := by
  decide

theorem S_all_squares : ∀ x ∈ S, ∃ k, x = k ^ 2 := by
  intro x hx
  fin_cases hx
  · exact ⟨1, by norm_num⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨3, by norm_num⟩
  · exact ⟨4, by norm_num⟩
  · exact ⟨5, by norm_num⟩
  · exact ⟨6, by norm_num⟩

#print axioms SidonSquares.S_sidon
#print axioms SidonSquares.S_all_squares

end SidonSquares
