import Mathlib

/-!
Frozen statement of the JSP-000731 / Erdős #880 target, against Mathlib only, with `sorry`.
NOT imported by the build; it is the challenge file for statement comparison.
-/

open Filter

namespace Erdos880Target

def IsSumOfAtMost (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ m : Multiset ℕ, (∀ a ∈ m, a ∈ A) ∧ Multiset.card m ≤ k ∧ m.sum = n

def distinctSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ A ∧ s.card ≤ k ∧ ∑ a ∈ s, a = n}

def IsAsymptoticBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ᶠ n in atTop, IsSumOfAtMost A k n

def HasBoundedGaps (B : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ᶠ n in atTop, ∃ b ∈ B, n ≤ b ∧ b ≤ n + C

/-- Burr–Erdős question, resolved by Hegyvári–Hennecart–Plagne (2007): the answer is yes for
`k = 2` and no for every `k ≥ 3` (even for bases of exact order `k` consisting of positive integers). -/
theorem erdos_880 :
    (∀ A : Set ℕ, IsAsymptoticBasis A 2 → HasBoundedGaps (distinctSums A 2)) ∧
    (∀ k : ℕ, 3 ≤ k → ∃ A : Set ℕ, A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧ IsAsymptoticBasis A k ∧
      (∀ j < k, ¬ IsAsymptoticBasis A j) ∧
      (distinctSums A k).Infinite ∧ ¬ HasBoundedGaps (distinctSums A k)) := by
  sorry

/-- Literal enumeration form: with `b i := Nat.nth (· ∈ distinctSums A k) i`. -/
theorem erdos_880_enumeration :
    (∀ A : Set ℕ, IsAsymptoticBasis A 2 → (distinctSums A 2).Infinite ∧
      ∃ C : ℕ, ∀ i : ℕ,
        Nat.nth (· ∈ distinctSums A 2) (i + 1) - Nat.nth (· ∈ distinctSums A 2) i ≤ C) ∧
    (∀ k : ℕ, 3 ≤ k → ∃ A : Set ℕ, A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧ IsAsymptoticBasis A k ∧
      (∀ j < k, ¬ IsAsymptoticBasis A j) ∧ (distinctSums A k).Infinite ∧
      ∀ C : ℕ, ∃ i : ℕ,
        C < Nat.nth (· ∈ distinctSums A k) (i + 1) - Nat.nth (· ∈ distinctSums A k) i) := by
  sorry

end Erdos880Target
