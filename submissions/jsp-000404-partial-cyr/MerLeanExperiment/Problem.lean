import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The ordinary planar minimax-angle problem, using indexed distinct points.
The mathematical classification is due to Blagovest Sendov (1995).
This file defines the problem; it does not assert its solution.
-/

namespace PlanarMinimax

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A real number bounds every angle of some configuration of `n` distinct points. -/
def RealizableCap (n : ℕ) (bound : ℝ) : Prop :=
  ∃ points : Fin n → Plane, Function.Injective points ∧
    ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      EuclideanGeometry.angle (points i) (points j) (points k) ≤ bound

/-- Infimum of the possible maximum-angle bounds for `n` distinct planar points. -/
noncomputable def minimaxAngle (n : ℕ) : ℝ :=
  sInf {bound : ℝ | RealizableCap n bound}

/-- The complete answer, including the two small cardinalities. -/
def SendovAnswer : Prop :=
  minimaxAngle 3 = Real.pi / 3 ∧
  minimaxAngle 4 = Real.pi / 2 ∧
  (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
    2 ^ m < n → n ≤ 2 ^ m + 2 ^ (m - 2) →
      minimaxAngle n = Real.pi * (1 - 2 / (2 * (m : ℝ) + 1))) ∧
  (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
    2 ^ m + 2 ^ (m - 2) < n → n ≤ 2 ^ (m + 1) →
      minimaxAngle n = Real.pi * (1 - 1 / ((m : ℝ) + 1)))

end PlanarMinimax
