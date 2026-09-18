import Mathlib

/-!
Frozen statement of the JSP-000825 / Erdős #992 target, against Mathlib only, with `sorry`.
NOT imported by the build; it freezes the statement for comparison with the proved roots.
-/

open MeasureTheory Filter Set

namespace Erdos992Target

def SubInterval : Type := {I : Set ℝ // I ⊆ Icc 0 1 ∧ I.OrdConnected}

open Classical in
noncomputable def count (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (I : Set ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ Int.fract (α * (x n : ℝ)) ∈ I).card

noncomputable def err (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (I : Set ℝ) : ℝ :=
  (count x α N I : ℝ) - (volume I).toReal * N

noncomputable def D (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup (Set.range fun I : SubInterval ↦ |err x α N I.1|)

def Erdos992Statement : Prop :=
  ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂volume, α ∈ Icc (0 : ℝ) 1 →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
        D x α N ≤ C * Real.sqrt N * Real.log N ^ ε

def Erdos992StatementLogLog : Prop :=
  ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂volume, α ∈ Icc (0 : ℝ) 1 →
      ∃ C K : ℝ, ∀ᶠ N : ℕ in atTop,
        D x α N ≤ C * Real.sqrt N * Real.log (Real.log N) ^ K

/-- Berkes–Philipp: a sequence whose discrepancy is `≫ (N log N)^{1/2}` infinitely often,
for almost all `α ∈ [0,1]`. -/
theorem berkes_philipp :
    ∃ x : ℕ → ℤ, StrictMono x ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᵐ α ∂volume, α ∈ Icc (0 : ℝ) 1 →
        ∃ᶠ N : ℕ in atTop, c * Real.sqrt (N * Real.log N) ≤ D x α N := by
  sorry

/-- The first question has the answer no. -/
theorem not_erdos_992 : ¬ Erdos992Statement := by
  sorry

/-- The "or even" question has the answer no. -/
theorem not_erdos_992_loglog : ¬ Erdos992StatementLogLog := by
  sorry

end Erdos992Target
