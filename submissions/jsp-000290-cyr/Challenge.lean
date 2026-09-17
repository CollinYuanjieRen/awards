/-
Comparator-style challenge module for JSP-000290 / Erdős Problem #348 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
`Proof/Main.lean` (the definitions below are the ones of `Proof/Main.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos348Challenge

/-- Every natural number is a sum of `a i` over a finite set of allowed indices `F ⊆ T`. -/
def Complete (a : ℕ → ℕ) (T : Set ℕ) : Prop :=
  ∀ x : ℕ, ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ T ∧ ∑ i ∈ F, a i = x

/-- `a` stays complete after removing any `m` indices. -/
def RobustlyComplete (a : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = m → Complete a (↑S : Set ℕ)ᶜ

theorem strongPairs_ge_two_eq_empty :
    {p : ℕ × ℕ | 2 ≤ p.1 ∧ p.1 < p.2 ∧ ∃ a : ℕ → ℕ, Monotone a ∧ (∀ i, 1 ≤ a i) ∧
      RobustlyComplete a p.1 ∧ ∀ S : Finset ℕ, S.card = p.2 → ¬ Complete a (↑S : Set ℕ)ᶜ} = ∅ := by
  sorry

theorem exists_infinite_removal (a : ℕ → ℕ) (ha : Monotone a) (hpos : ∀ i, 1 ≤ a i) (m : ℕ)
    (hm : 2 ≤ m) (h : RobustlyComplete a m) : ∃ R : Set ℕ, R.Infinite ∧ Complete a Rᶜ := by
  sorry

theorem exists_removal_card (a : ℕ → ℕ) (ha : Monotone a) (hpos : ∀ i, 1 ≤ a i) (m : ℕ)
    (hm : 2 ≤ m) (h : RobustlyComplete a m) (n : ℕ) :
    ∃ S : Finset ℕ, S.card = n ∧ Complete a (↑S : Set ℕ)ᶜ := by
  sorry

end Erdos348Challenge
