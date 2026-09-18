import Mathlib

/-!
# JSP-000990 / Erdős #1185 — definitions

Erdős–Mauldin [Er80, p. 92]: let `δ > 0` and `k ≥ 3`.  Is it true that there exists `m ≥ 1`
(depending only on `δ` and `k`) such that, for all large `N`, if `A, B ⊆ {1, …, N}` with
`|A| ≥ δN` and `|B| ≥ m` then there is a non-trivial `k`-term arithmetic progression in `A` whose
common difference is in `B − B`?  The answer is **no**, already for `k = 3` (Furstenberg 1981).
-/

open Finset

namespace Erdos1185

/-- `A` contains a non-trivial `k`-term arithmetic progression `a, a + d, …, a + (k-1)d`
(`d > 0`) whose common difference `d` is a difference `b₁ − b₂` of two elements of `B`. -/
def HasAPWithStepInDiff (k : ℕ) (A B : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ (∀ j : ℕ, j < k → a + j * d ∈ A) ∧ ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₂ + d = b₁

/-- The universal statement asked in Erdős Problem #1185 (with "for all large `N`" read as
"for all `N ≥ N₀` for some `N₀`"). -/
def Erdos1185Statement : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
        δ * (N : ℝ) ≤ (#A : ℝ) → m ≤ #B → HasAPWithStepInDiff k A B

end Erdos1185
