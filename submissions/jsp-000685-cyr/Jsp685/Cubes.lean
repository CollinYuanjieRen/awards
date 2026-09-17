import Mathlib

namespace TwoCubes

/-- The set of representations of `n` as `a^3 + b^3` with `1 ≤ a ≤ b ≤ bound`. -/
def cubeReps (n bound : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 bound) ×ˢ (Finset.Icc 1 bound)).filter
    (fun p => p.1 ≤ p.2 ∧ p.1 ^ 3 + p.2 ^ 3 = n)

theorem two_le_card_cubeReps_1729 : 2 ≤ (cubeReps 1729 12).card := by
  have h : ({(1, 12), (9, 10)} : Finset (ℕ × ℕ)) ⊆ cubeReps 1729 12 := by
    intro p hp
    fin_cases hp <;>
      · simp only [cubeReps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> decide
  calc 2 = ({(1, 12), (9, 10)} : Finset (ℕ × ℕ)).card := by decide
    _ ≤ (cubeReps 1729 12).card := Finset.card_le_card h

theorem exists_two_cube_representations :
    ∃ p q : ℕ × ℕ, p ≠ q ∧ p.1 ≤ p.2 ∧ q.1 ≤ q.2 ∧
      p.1 ^ 3 + p.2 ^ 3 = 1729 ∧ q.1 ^ 3 + q.2 ^ 3 = 1729 := by
  refine ⟨(1, 12), (9, 10), ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#print axioms TwoCubes.two_le_card_cubeReps_1729
#print axioms TwoCubes.exists_two_cube_representations

end TwoCubes
