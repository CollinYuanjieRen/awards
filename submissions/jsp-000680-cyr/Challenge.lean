import Mathlib

/-! Comparator-style challenge module (Mathlib-only; target with `sorry`, not imported by the build)
for JSP-000680 / Erdős #824, the finite lower bound h(18) ≥ 3. -/

namespace Challenge824

/-- `h x` counts coprime pairs `1 ≤ a < b < x` with `σ(a) = σ(b)` (`σ = sum of divisors`). -/
def h (x : ℕ) : ℕ :=
  (((Finset.Ico 1 x) ×ˢ (Finset.Ico 1 x)).filter
    (fun p => p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
      ArithmeticFunction.sigma 1 p.1 = ArithmeticFunction.sigma 1 p.2)).card

theorem three_le_h_eighteen : 3 ≤ h 18 := by
  sorry

end Challenge824
