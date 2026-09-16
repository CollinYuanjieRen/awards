import Jsp285.FiniteConstants

/-! Absolute counting coefficient for the occurrence-indexed infinite extension. -/

namespace Jsp285

/-- Slack in the selected sequences makes the finite AP steps small. -/
def infiniteScale : ℕ := 64 * finiteCoefficient ^ 2

/-- The original eventual counting hypothesis will use this absolute coefficient. -/
def infiniteCoefficient : ℕ := 8 * infiniteScale

/-- The finite coefficient is positive. -/
lemma finiteCoefficient_pos : 0 < finiteCoefficient := by
  norm_num [finiteCoefficient, partitionMass]

/-- The selected-sequence scale is positive. -/
lemma infiniteScale_pos : 0 < infiniteScale := by
  unfold infiniteScale
  have := finiteCoefficient_pos
  positivity

/-- The scale is large enough to keep every selected block within its AP target box. -/
lemma two_mul_finiteCoefficient_le_infiniteScale :
    2 * finiteCoefficient ≤ infiniteScale := by
  have := finiteCoefficient_pos
  unfold infiniteScale
  nlinarith [Nat.le_mul_self finiteCoefficient]

/-- At least a factor of two is available for the reservoir growth argument. -/
lemma two_le_infiniteScale : 2 ≤ infiniteScale := by
  have := finiteCoefficient_pos
  have := two_mul_finiteCoefficient_le_infiniteScale
  omega

/-- The final counting coefficient is strictly positive. -/
lemma infiniteCoefficient_pos : 0 < infiniteCoefficient := by
  unfold infiniteCoefficient
  exact Nat.mul_pos (by omega) infiniteScale_pos

end Jsp285
