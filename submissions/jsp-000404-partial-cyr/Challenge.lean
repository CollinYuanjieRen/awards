import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Comparator-style challenge module (Mathlib-only; the definitions of `Problem.lean` restated
(token-identical, reflowed), plus the full Sendov answer and this package's proved scoped target, each with `sorry`;
not imported by the build) for JSP-000404 / Erdős #504.

`Challenge504.sendov_partial` is exactly the theorem proved in `MerLeanExperiment/SendovPartial.lean`.
`Challenge504.SendovAnswer` is the full classification, restated here only to record precisely what
is NOT claimed: its two general sharp lower branches (for non-dyadic `n` with `m ≥ 4`) are left open. -/

namespace Challenge504

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def RealizableCap (n : ℕ) (bound : ℝ) : Prop :=
  ∃ points : Fin n → Plane, Function.Injective points ∧
    ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      EuclideanGeometry.angle (points i) (points j) (points k) ≤ bound

noncomputable def minimaxAngle (n : ℕ) : ℝ := sInf {bound : ℝ | RealizableCap n bound}

/-- Sendov's full 1995 classification (NOT claimed by this package; recorded for comparison). -/
def SendovAnswer : Prop :=
  minimaxAngle 3 = Real.pi / 3 ∧
  minimaxAngle 4 = Real.pi / 2 ∧
  (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
    2 ^ m < n → n ≤ 2 ^ m + 2 ^ (m - 2) →
      minimaxAngle n = Real.pi * (1 - 2 / (2 * (m : ℝ) + 1))) ∧
  (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
    2 ^ m + 2 ^ (m - 2) < n → n ≤ 2 ^ (m + 1) →
      minimaxAngle n = Real.pi * (1 - 1 / ((m : ℝ) + 1)))

theorem sendov_partial :
    (minimaxAngle 3 = Real.pi / 3 ∧ minimaxAngle 4 = Real.pi / 2) ∧
    minimaxAngle 5 = 3 * Real.pi / 5 ∧
    (∀ N : ℕ, 6 ≤ N → N ≤ 8 → minimaxAngle N = 2 * Real.pi / 3) ∧
    (∀ k : ℕ, 2 ≤ k → minimaxAngle (2 ^ k) = Real.pi * (1 - 1 / (k : ℝ))) ∧
    ((∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
        2 ^ m < n → n ≤ 2 ^ m + 2 ^ (m - 2) →
          minimaxAngle n ≤ Real.pi * (1 - 2 / (2 * (m : ℝ) + 1))) ∧
     (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
        2 ^ m + 2 ^ (m - 2) < n → n ≤ 2 ^ (m + 1) →
          minimaxAngle n ≤ Real.pi * (1 - 1 / ((m : ℝ) + 1)))) := by
  sorry

end Challenge504
