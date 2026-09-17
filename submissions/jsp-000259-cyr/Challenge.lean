import Mathlib

/-! Comparator-style challenge module (Mathlib-only; targets with `sorry`, not imported by the build)
for JSP-000259 / Erdős #308, the N=6 representable-set instance. -/

namespace Challenge308

/-- `k` is representable with denominators from `{1,…,N}`. -/
def Representable (N k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ ∑ n ∈ S, (1 : ℚ) / n = k

/-- the representable positive integers for `N = 6` are exactly `{1, 2}`. -/
theorem representable_six_iff {k : ℕ} (hk : 1 ≤ k) : Representable 6 k ↔ k = 1 ∨ k = 2 := by
  sorry

end Challenge308
