import Mathlib

/-!
Frozen statement of the JSP-000990 / Erdős #1185 target, against Mathlib only, with `sorry`.
NOT imported by the build; it freezes the statement for comparison with the proved roots.
-/

open Finset

namespace Erdos1185Target

def HasAPWithStepInDiff (k : ℕ) (A B : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ (∀ j : ℕ, j < k → a + j * d ∈ A) ∧ ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₂ + d = b₁

def Erdos1185Statement : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
        δ * (N : ℝ) ≤ (#A : ℝ) → m ≤ #B → HasAPWithStepInDiff k A B

/-- The negative resolution (Furstenberg): the statement fails, already for `k = 3`. -/
theorem not_erdos_1185 : ¬ Erdos1185Statement := by
  sorry

/-- Explicit counterexamples for every `k ≥ 3` and every `δ ≤ 1/64`. -/
theorem counterexample (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : δ ≤ 1 / 64) (m N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ A B : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧
      δ * (N : ℝ) ≤ (#A : ℝ) ∧ m ≤ #B ∧ ¬ HasAPWithStepInDiff k A B := by
  sorry

end Erdos1185Target
