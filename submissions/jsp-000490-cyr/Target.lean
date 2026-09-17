import Mathlib

/-!
Frozen statement of the JSP-000490 / Erdős #603 target, against Mathlib only, with `sorry`.
NOT imported by the build; it freezes the statement for comparison with the proved roots.
-/

universe u

open Cardinal

namespace Erdos603Target

def AlwaysColourable (C : Cardinal.{u}) : Prop :=
  ∀ (X : Type u) (𝒜 : Set (Set X)), (∀ A ∈ 𝒜, A.Countable ∧ A.Infinite) →
    (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → (A ∩ B).encard ≠ 2) →
    ∃ (Y : Type u) (col : ⋃₀ 𝒜 → Y), #Y ≤ C ∧
      ∀ A ∈ 𝒜, ∃ x y : ⋃₀ 𝒜, (x : X) ∈ A ∧ (y : X) ∈ A ∧ col x ≠ col y

/-- For every cardinal `C` there is a family of countably infinite sets, pairwise never meeting in
exactly two elements and covering its ground set, such that every colouring with at most `C`
colours makes some member monochromatic. -/
theorem erdos_603 (C : Cardinal.{u}) : ∃ (X : Type u) (𝒜 : Set (Set X)),
    (∀ A ∈ 𝒜, A.Countable ∧ A.Infinite) ∧
    (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → (A ∩ B).encard ≠ 2) ∧
    (∀ x : X, ∃ A ∈ 𝒜, x ∈ A) ∧
    ∀ (Y : Type u) (col : X → Y), #Y ≤ C → ∃ A ∈ 𝒜, ∀ x ∈ A, ∀ y ∈ A, col x = col y := by
  sorry

/-- No cardinal suffices, hence there is no smallest sufficient cardinal. -/
theorem not_alwaysColourable (C : Cardinal.{u}) : ¬ AlwaysColourable C := by
  sorry

theorem no_least_cardinal : ¬ ∃ C : Cardinal.{u}, IsLeast {C | AlwaysColourable C} C := by
  sorry

end Erdos603Target
