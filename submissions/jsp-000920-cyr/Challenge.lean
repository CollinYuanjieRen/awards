import Mathlib

/-! Comparator-style challenge module (Mathlib-only; targets with `sorry`, not imported by the build)
for JSP-000920 / Erdős #1109, the elementary structural upper bound for squarefree sumsets. -/

namespace Challenge1109

/-- every pairwise sum of `A` (including `a + a`) is squarefree -/
def SquarefreeSumset (A : Finset ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)

/-- a squarefree-sumset set lies in a single residue class mod 4. -/
theorem single_class_mod_four {A : Finset ℕ} (h : SquarefreeSumset A) :
    (∀ a ∈ A, a % 4 = 1) ∨ (∀ a ∈ A, a % 4 = 3) := by
  sorry

/-- the elementary upper bound `4·|A| ≤ N + 3` for `A ⊆ {1,…,N}`. -/
theorem card_le {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (h : SquarefreeSumset A) :
    4 * A.card ≤ N + 3 := by
  sorry

end Challenge1109
