import MerLeanExperiment.DirectionFrame
import Mathlib.Tactic

/-!
Explicit planar rotations used as supporting coordinate normalizations.
This module does not assert any sharp minimax bound.
-/

namespace PlanarMinimax

/-- Clockwise rotation through angle `φ`. -/
noncomputable def rotatePlane (φ : ℝ) (v : Plane) : Plane :=
  !₂[Real.cos φ * v 0 + Real.sin φ * v 1,
    -Real.sin φ * v 0 + Real.cos φ * v 1]

theorem rotatePlane_add (φ : ℝ) (v w : Plane) :
    rotatePlane φ (v + w) = rotatePlane φ v + rotatePlane φ w := by
  ext i
  fin_cases i <;> simp [rotatePlane] <;> ring

theorem rotatePlane_sub (φ : ℝ) (v w : Plane) :
    rotatePlane φ (v - w) = rotatePlane φ v - rotatePlane φ w := by
  ext i
  fin_cases i <;> simp [rotatePlane] <;> ring

theorem rotatePlane_smul (φ r : ℝ) (v : Plane) :
    rotatePlane φ (r • v) = r • rotatePlane φ v := by
  ext i
  fin_cases i <;> simp [rotatePlane] <;> ring

theorem inner_rotatePlane (φ : ℝ) (v w : Plane) :
    inner ℝ (rotatePlane φ v) (rotatePlane φ w) = inner ℝ v w := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two]
  simp [rotatePlane]
  linear_combination (v 0 * w 0 + v 1 * w 1) * Real.sin_sq_add_cos_sq φ

theorem norm_rotatePlane (φ : ℝ) (v : Plane) : ‖rotatePlane φ v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simpa [norm_sq_eq_re_inner] using inner_rotatePlane φ v v

theorem rotatePlane_injective (φ : ℝ) : Function.Injective (rotatePlane φ) := by
  intro v w hvw
  have hz : rotatePlane φ (v - w) = 0 := by
    rw [rotatePlane_sub, hvw, sub_self]
  have hn : ‖v - w‖ = 0 := by
    rw [← norm_rotatePlane φ, hz, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem rotatePlane_unitDirection (φ θ : ℝ) :
    rotatePlane φ (unitDirection θ) = unitDirection (θ - φ) := by
  ext i
  fin_cases i
  · simp [rotatePlane, unitDirection, Real.cos_sub]
    ring
  · simp [rotatePlane, unitDirection, Real.sin_sub]
    ring

theorem angle_rotatePlane (φ : ℝ) (v w : Plane) :
    InnerProductGeometry.angle (rotatePlane φ v) (rotatePlane φ w) =
      InnerProductGeometry.angle v w := by
  unfold InnerProductGeometry.angle
  rw [inner_rotatePlane, norm_rotatePlane, norm_rotatePlane]

theorem euclideanAngle_rotatePlane (φ : ℝ) (a b c : Plane) :
    EuclideanGeometry.angle (rotatePlane φ a) (rotatePlane φ b) (rotatePlane φ c) =
      EuclideanGeometry.angle a b c := by
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub, ← rotatePlane_sub]
  exact angle_rotatePlane φ (a - b) (c - b)

#print axioms rotatePlane_add
#print axioms rotatePlane_sub
#print axioms rotatePlane_smul
#print axioms norm_rotatePlane
#print axioms rotatePlane_injective
#print axioms rotatePlane_unitDirection
#print axioms angle_rotatePlane
#print axioms euclideanAngle_rotatePlane

end PlanarMinimax
