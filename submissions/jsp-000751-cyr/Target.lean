import Mathlib

/-!
Frozen statement of the JSP-000751 / Erdős #903 target, against Mathlib only, with `sorry`.
NOT imported by the build; it freezes the statement for comparison with the proved roots.
-/

open Finset

namespace Erdos903Target

/-- A pairwise balanced design of index one (linear space): blocks have at least two points and
every pair of distinct points lies in exactly one block. -/
def IsLinearSpace {v b : ℕ} (block : Fin b → Finset (Fin v)) : Prop :=
  (∀ i, 2 ≤ #(block i)) ∧ ∀ x y : Fin v, x ≠ y → ∃! i, x ∈ block i ∧ y ∈ block i

/-- Erdős–Fowler–Sós–Wilson, Theorem 2 (every `p`): on `p² + p + 1` points, more than `p² + p + 1`
blocks forces at least `p² + 2p + 1` blocks. -/
theorem erdos_903_general (p b : ℕ) (block : Fin b → Finset (Fin (p ^ 2 + p + 1)))
    (h : IsLinearSpace block) (hb : p ^ 2 + p + 1 < b) : p ^ 2 + p + 1 + p ≤ b := by
  sorry

/-- The problem page's form, for prime powers `p`. -/
theorem erdos_903 (p b : ℕ) (hp : IsPrimePow p) (block : Fin b → Finset (Fin (p ^ 2 + p + 1)))
    (h : IsLinearSpace block) (hb : p ^ 2 + p + 1 < b) : p ^ 2 + p + 1 + p ≤ b := by
  sorry

end Erdos903Target
