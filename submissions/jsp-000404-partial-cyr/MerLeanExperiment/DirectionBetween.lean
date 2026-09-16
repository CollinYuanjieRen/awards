import MerLeanExperiment.DirectionFrame

/-!
Positive planar combinations of directions in the upper half-plane have an
angular parameter between those of the summands.
-/

namespace PlanarMinimax

/-- The oriented planar determinant. -/
def directionDet (v w : Plane) : ℝ := v 0 * w 1 - v 1 * w 0

private theorem directionDet_smul_right (v w : Plane) (a : ℝ) :
    directionDet v (a • w) = a * directionDet v w := by
  simp [directionDet]
  ring

private theorem directionDet_smul_left (v w : Plane) (a : ℝ) :
    directionDet (a • v) w = a * directionDet v w := by
  simp [directionDet]
  ring

private theorem directionDet_add_right (u v w : Plane) :
    directionDet u (v + w) = directionDet u v + directionDet u w := by
  simp [directionDet]
  ring

private theorem directionDet_add_left (u v w : Plane) :
    directionDet (u + v) w = directionDet u w + directionDet v w := by
  simp [directionDet]
  ring

private theorem directionDet_self (v : Plane) : directionDet v v = 0 := by
  simp [directionDet]
  ring

theorem directionDet_unitDirection (α β : ℝ) :
    directionDet (unitDirection α) (unitDirection β) = Real.sin (β - α) := by
  simp [directionDet, unitDirection, Real.sin_sub]
  ring

theorem directionDet_unitDirection_nonneg_iff {α β : ℝ}
    (hα : 0 ≤ α) (hαpi : α < Real.pi) (hβ : 0 ≤ β) (hβpi : β < Real.pi) :
    0 ≤ directionDet (unitDirection α) (unitDirection β) ↔ α ≤ β := by
  rw [directionDet_unitDirection]
  constructor
  · intro hdet
    by_contra hnot
    have hneg : Real.sin (β - α) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (sub_neg.2 (lt_of_not_ge hnot)) (by linarith)
    linarith
  · intro hab
    rcases hab.eq_or_lt with rfl | hab
    · simp
    · exact (Real.sin_pos_of_pos_of_lt_pi (sub_pos.2 hab) (by linarith)).le

/-- A positive combination direction lies between its two summand directions. -/
theorem direction_between {α β γ a b c : ℝ}
    (hα : 0 ≤ α) (hαpi : α < Real.pi)
    (hβ : 0 ≤ β) (hβpi : β < Real.pi)
    (hγ : 0 ≤ γ) (hγpi : γ < Real.pi)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (heq : c • unitDirection γ =
      a • unitDirection α + b • unitDirection β) :
    (α ≤ γ ∧ γ ≤ β) ∨ (β ≤ γ ∧ γ ≤ α) := by
  have hαγ : c * directionDet (unitDirection α) (unitDirection γ) =
      b * directionDet (unitDirection α) (unitDirection β) := by
    calc
      c * directionDet (unitDirection α) (unitDirection γ) =
          directionDet (unitDirection α) (c • unitDirection γ) := by
            rw [directionDet_smul_right]
      _ = directionDet (unitDirection α)
          (a • unitDirection α + b • unitDirection β) := by rw [heq]
      _ = b * directionDet (unitDirection α) (unitDirection β) := by
        rw [directionDet_add_right, directionDet_smul_right,
          directionDet_smul_right, directionDet_self]
        ring
  have hγβ : c * directionDet (unitDirection γ) (unitDirection β) =
      a * directionDet (unitDirection α) (unitDirection β) := by
    calc
      c * directionDet (unitDirection γ) (unitDirection β) =
          directionDet (c • unitDirection γ) (unitDirection β) := by
            rw [directionDet_smul_left]
      _ = directionDet (a • unitDirection α + b • unitDirection β)
          (unitDirection β) := by rw [heq]
      _ = a * directionDet (unitDirection α) (unitDirection β) := by
        rw [directionDet_add_left, directionDet_smul_left,
          directionDet_smul_left, directionDet_self]
        ring
  rcases le_total α β with hab | hba
  · left
    have hdab : 0 ≤ directionDet (unitDirection α) (unitDirection β) :=
      (directionDet_unitDirection_nonneg_iff hα hαpi hβ hβpi).2 hab
    constructor
    · apply (directionDet_unitDirection_nonneg_iff hα hαpi hγ hγpi).1
      nlinarith
    · apply (directionDet_unitDirection_nonneg_iff hγ hγpi hβ hβpi).1
      nlinarith
  · right
    have hdba : 0 ≤ directionDet (unitDirection β) (unitDirection α) :=
      (directionDet_unitDirection_nonneg_iff hβ hβpi hα hαpi).2 hba
    have hdab : directionDet (unitDirection α) (unitDirection β) =
        -directionDet (unitDirection β) (unitDirection α) := by
      simp [directionDet]
      ring
    constructor
    · apply (directionDet_unitDirection_nonneg_iff hβ hβpi hγ hγpi).1
      have hβγ : c * directionDet (unitDirection β) (unitDirection γ) =
          a * directionDet (unitDirection β) (unitDirection α) := by
        rw [show directionDet (unitDirection β) (unitDirection γ) =
            -directionDet (unitDirection γ) (unitDirection β) by
          simp [directionDet]
          ring]
        rw [hdab] at hγβ
        linarith
      nlinarith
    · apply (directionDet_unitDirection_nonneg_iff hγ hγpi hα hαpi).1
      have hγα : c * directionDet (unitDirection γ) (unitDirection α) =
          b * directionDet (unitDirection β) (unitDirection α) := by
        rw [show directionDet (unitDirection γ) (unitDirection α) =
            -directionDet (unitDirection α) (unitDirection γ) by
          simp [directionDet]
          ring]
        rw [hdab] at hαγ
        linarith
      nlinarith

#print axioms directionDet_unitDirection
#print axioms directionDet_unitDirection_nonneg_iff
#print axioms direction_between

end PlanarMinimax
