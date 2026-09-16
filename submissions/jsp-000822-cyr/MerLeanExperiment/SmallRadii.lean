import MerLeanExperiment.RadiusTransfer

namespace DiskDiscrepancy


/-- Monotonicity bounds the discrepancy in any smaller concentric disk. -/
theorem discrepancy_le_of_le_radius {A : Set Plane} (hA : Admissible A)
    {x : Plane} {r s D : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hD : discrepancy A x s ≤ D) :
    discrepancy A x r ≤ D + 2 * Real.pi * s ^ 2 := by
  have hs : 0 ≤ s := hr.trans hrs
  have hcountNat : pointCount A x r ≤ pointCount A x s :=
    pointCount_le_of_closedBall_subset hA (Metric.closedBall_subset_closedBall hrs)
  have hcount : (pointCount A x r : ℝ) ≤ pointCount A x s := by
    exact_mod_cast hcountNat
  have hD0 : 0 ≤ D := (discrepancy_nonneg A x s).trans hD
  have harea : Real.pi * r ^ 2 ≤ Real.pi * s ^ 2 :=
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ hr hs).mpr hrs) Real.pi_pos.le
  have hcount0 : (0 : ℝ) ≤ pointCount A x r := Nat.cast_nonneg _
  have hsarea : 0 ≤ Real.pi * s ^ 2 := mul_nonneg Real.pi_pos.le (sq_nonneg s)
  change |(pointCount A x s : ℝ) - Real.pi * s ^ 2| ≤ D at hD
  have hupper := (abs_le.mp hD).2
  change |(pointCount A x r : ℝ) - Real.pi * r ^ 2| ≤ D + 2 * Real.pi * s ^ 2
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg r)]

/-- Control of radii between four and the outer scale controls all positive radii. -/
theorem all_positive_radii_of_four_le {A : Set Plane} (hA : Admissible A)
    {R D : ℝ} (hR : 4 ≤ R)
    (hbound : ∀ x : Plane, ∀ r : ℝ, 4 ≤ r → r ≤ R → discrepancy A x r ≤ D) :
    ∀ x : Plane, ∀ r : ℝ, 0 < r → r ≤ R →
      discrepancy A x r ≤ D + 32 * Real.pi := by
  intro x r hr hrR
  by_cases hr4 : r ≤ 4
  · have h := discrepancy_le_of_le_radius hA hr.le hr4 (hbound x 4 le_rfl hR)
    nlinarith
  · have h := hbound x r (le_of_not_ge hr4) hrR
    linarith [Real.pi_pos]

end DiskDiscrepancy
