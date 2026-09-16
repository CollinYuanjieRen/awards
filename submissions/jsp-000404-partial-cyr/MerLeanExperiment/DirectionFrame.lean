import MerLeanExperiment.Problem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
Elementary planar direction frames used by later limiting constructions.
-/

namespace PlanarMinimax

/-- The unit vector making angle `θ` with the positive horizontal axis. -/
noncomputable def unitDirection (θ : ℝ) : Plane :=
  !₂[Real.cos θ, Real.sin θ]

theorem norm_unitDirection (θ : ℝ) : ‖unitDirection θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [unitDirection, Fin.sum_univ_two]

theorem unitDirection_ne_zero (θ : ℝ) : unitDirection θ ≠ 0 := by
  intro h
  have := norm_unitDirection θ
  rw [h, norm_zero] at this
  norm_num at this

theorem inner_unitDirection (θ φ : ℝ) :
    inner ℝ (unitDirection θ) (unitDirection φ) = Real.cos (θ - φ) := by
  simp [unitDirection, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub,
    mul_comm]

theorem angle_unitDirection (θ φ : ℝ) (h : |θ - φ| ≤ Real.pi) :
    InnerProductGeometry.angle (unitDirection θ) (unitDirection φ) = |θ - φ| := by
  unfold InnerProductGeometry.angle
  rw [norm_unitDirection, norm_unitDirection, mul_one, div_one,
    inner_unitDirection, ← Real.cos_abs]
  exact Real.arccos_cos (abs_nonneg _) h

/-- A choice of either orientation of a unit direction. -/
noncomputable def signedDirection (σ : Bool) (θ : ℝ) : Plane :=
  if σ then unitDirection θ else -unitDirection θ

theorem signedDirection_ne_zero (σ : Bool) (θ : ℝ) :
    signedDirection σ θ ≠ 0 := by
  cases σ <;> simp [signedDirection, unitDirection_ne_zero]

theorem angle_signedDirection_le (σ τ : Bool) (θ φ δ : ℝ)
    (hδ : 0 ≤ δ) (hlower : δ ≤ |θ - φ|)
    (hupper : |θ - φ| ≤ Real.pi - δ) :
    InnerProductGeometry.angle (signedDirection σ θ) (signedDirection τ φ) ≤
      Real.pi - δ := by
  have habspi : |θ - φ| ≤ Real.pi := by
    linarith
  have hangle := angle_unitDirection θ φ habspi
  cases σ <;> cases τ
  · change InnerProductGeometry.angle (-unitDirection θ) (-unitDirection φ) ≤ _
    rw [InnerProductGeometry.angle_neg_neg, hangle]
    exact hupper
  · change InnerProductGeometry.angle (-unitDirection θ) (unitDirection φ) ≤ _
    rw [InnerProductGeometry.angle_neg_left, hangle]
    linarith
  · change InnerProductGeometry.angle (unitDirection θ) (-unitDirection φ) ≤ _
    rw [InnerProductGeometry.angle_neg_right, hangle]
    linarith
  · change InnerProductGeometry.angle (unitDirection θ) (unitDirection φ) ≤ _
    rwa [hangle]

/-- The `i`th direction in a regular half-circle frame of size `k`. -/
noncomputable def frameAngle (k : ℕ) (i : Fin k) : ℝ :=
  (i : ℝ) * Real.pi / k

theorem frameAngle_separation {k : ℕ} (hk : 2 ≤ k) {i j : Fin k} (hij : i ≠ j) :
    Real.pi / k ≤ |frameAngle k i - frameAngle k j| ∧
      |frameAngle k i - frameAngle k j| ≤ Real.pi - Real.pi / k := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij'
    have hjbound : (j : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast j.isLt
    rw [abs_of_nonpos]
    · constructor <;> (unfold frameAngle; field_simp; nlinarith)
    · unfold frameAngle
      rw [← sub_div]
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · positivity
  · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hji'
    have hibound : (i : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast i.isLt
    rw [abs_of_nonneg]
    · constructor <;> (unfold frameAngle; field_simp; nlinarith)
    · unfold frameAngle
      rw [← sub_div]
      apply div_nonneg
      · nlinarith
      · positivity

theorem angle_signed_frame_le {k : ℕ} (hk : 2 ≤ k) {i j : Fin k} (hij : i ≠ j)
    (σ τ : Bool) :
    InnerProductGeometry.angle
        (signedDirection σ (frameAngle k i)) (signedDirection τ (frameAngle k j)) ≤
      Real.pi - Real.pi / k := by
  exact angle_signedDirection_le σ τ _ _ _ (by positivity)
    (frameAngle_separation hk hij).1 (frameAngle_separation hk hij).2

#print axioms norm_unitDirection
#print axioms unitDirection_ne_zero
#print axioms inner_unitDirection
#print axioms angle_unitDirection
#print axioms signedDirection_ne_zero
#print axioms angle_signedDirection_le
#print axioms frameAngle_separation
#print axioms angle_signed_frame_le

end PlanarMinimax
