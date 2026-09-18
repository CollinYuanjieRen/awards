import Mathlib

/-!
Frozen statement of the JSP-001010 / Erdős #1205 target, against Mathlib only, with `sorry`.
NOT imported by the build; it freezes the statement for comparison with the proved roots.
-/

open Finset Filter Topology

namespace Erdos1205Target

def coverCount (a : ℕ → ℕ) (x m : ℕ) : ℕ :=
  ((Icc 1 x).filter fun n => m % n = a n % n).card

noncomputable def F (x : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : ℕ → ℕ, ∀ m ∈ Icc 1 x, k ≤ coverCount a x m}

/-- The resolution recorded on erdosproblems.com/1205:
`log x − O(√(log x · log log x)) ≤ F(x) ≤ log x + O(1)`, hence `F(x) ∼ log x`. -/
theorem erdos_1205 :
    (∀ x : ℕ, 1 ≤ x → (F x : ℝ) ≤ Real.log x + 2) ∧
    (∃ C : ℝ, ∀ᶠ x : ℕ in atTop,
      Real.log x - C * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ F x) ∧
    Tendsto (fun x : ℕ => (F x : ℝ) / Real.log x) atTop (𝓝 1) := by
  sorry

end Erdos1205Target
