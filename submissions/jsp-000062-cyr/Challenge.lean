import Mathlib
/-!
Mathlib-only comparator for JSP-000062 / Erdős #30 (scoped: elementary Erdős-Turán bound).
Restates the definitions and targets against pure Mathlib; the real proofs live in `Jsp062/Sidon.lean`.
This file is NOT imported by the build; it exists so a reviewer can confirm the statements are faithful.
-/
namespace Erdos30Challenge

def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → a = c ∨ a = d

theorem choose_two_le {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon A) :
    A.card.choose 2 ≤ N - 1 := by
  sorry

theorem card_mul_pred_le {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon A) :
    A.card * (A.card - 1) ≤ 2 * (N - 1) := by
  sorry

end Erdos30Challenge
