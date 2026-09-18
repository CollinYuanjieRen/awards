import Mathlib

/-!
# The closed unit-disk model for exterior roots

This module contains the elementary change of variables used throughout the
Luo--Yang--Zhu proof.  An exterior root has a reciprocal in the closed unit
disk.  The compact subtype is also the state space for the empirical measures
in the Cauchy-transform argument.
-/

open Metric Set

namespace Erdos973

/-- The closed unit disk, used as a compact measurable state space. -/
abbrev UnitDisk := Metric.closedBall (0 : ℂ) 1

noncomputable instance : CompactSpace UnitDisk :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)

/-- The reciprocal of an exterior point belongs to the closed unit disk. -/
theorem inv_mem_unitDisk {z : ℂ} (hz : 1 ≤ ‖z‖) : z⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall, dist_zero_right, norm_inv]
  exact (inv_le_one₀ (by positivity)).2 hz

/-- Package the reciprocal of an exterior point as a point of `UnitDisk`. -/
noncomputable def reciprocalDiskPoint (z : ℂ) (hz : 1 ≤ ‖z‖) : UnitDisk :=
  ⟨z⁻¹, inv_mem_unitDisk hz⟩

@[simp] theorem coe_reciprocalDiskPoint (z : ℂ) (hz : 1 ≤ ‖z‖) :
    (reciprocalDiskPoint z hz : ℂ) = z⁻¹ := rfl

end Erdos973
