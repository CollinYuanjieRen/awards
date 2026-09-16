import Mathlib

/-!
Comparator-style challenge module for JSP-000827 / Erdős #994: Mathlib-only definitions and
the target statement with `sorry`, for mechanical statement comparison against
`Jsp827.Root` (`Erdos994.not_khintchineFixedSet`, whose definitions are byte-identical).
This file is intentionally NOT imported by the package build.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Challenge994

attribute [local instance] Classical.propDecidable

/-- The normalized number of visits of the fractional parts
`fract (k * α)`, `1 ≤ k ≤ n`, to `E`.  At `n = 0` this is `0`. -/
noncomputable def visitAverage (E : Set ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n,
      if Int.fract ((k : ℝ) * α) ∈ E then (1 : ℝ) else 0) / (n : ℝ)

/-- The visit averages for `E` and `α` converge to the Lebesgue measure of `E`. -/
def HasExpectedLimit (E : Set ℝ) (α : ℝ) : Prop :=
  Tendsto (visitAverage E α) atTop (𝓝 (volume E).toReal)

/-- Khintchine's conjecture (fixed-set quantifier order): for every measurable `E ⊆ (0,1)`,
almost every `α` has the expected limit. -/
def KhintchineFixedSet : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo (0 : ℝ) 1 →
    ∀ᵐ α : ℝ, HasExpectedLimit E α

/-- Target: Khintchine's conjecture is false (Marstrand 1970). -/
theorem not_khintchineFixedSet : ¬ KhintchineFixedSet := by
  sorry

end Challenge994
