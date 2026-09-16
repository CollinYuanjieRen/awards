import MerLeanExperiment.JitterTail
import MerLeanExperiment.CellQuadrature

open MeasureTheory

namespace DiskDiscrepancy

/-- The actual periodic sample's expected count is the normalized global midpoint-grid count. -/
theorem jitter_count_expectation_eq_midpointGridArea (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (center : Plane) {radius : ℝ} (hr : 0 ≤ radius) :
    (∫ ω, (pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) ∂jitterMeasure L q hq) =
      midpointGridArea q center radius := by
  simp_rw [pointCount_periodicGridSet_real_eq_sum_cellHit L q hL hq _ center hr]
  rw [integral_finsetSum _ (fun z _ ↦ integrable_sampled_cellHit L q hL hq center radius z
    (jitterMeasure L q hq))]
  exact sum_cellHit_expectation_eq_midpointGridArea L q hL hq center hr

/-- Uniform disk discrepancy has a small bad-event probability for the actual finite jitter model. -/
theorem jitter_discrepancy_tail (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (center : Plane) {radius R : ℝ} (hR : 4 ≤ R) (hqR : R ≤ q)
    (hr : 0 ≤ radius) (hrR : radius ≤ R + 1) (hperiod : 2 * radius + 1 < L) :
    (jitterMeasure L q hq).real {ω |
      30 * Real.sqrt (R * Real.log R) + 256 ≤
        discrepancy (periodicGridSet L q hL hq ω) center radius} ≤ 2 / R ^ 15 := by
  let μ := jitterMeasure L q hq
  let m := ∫ ω, (pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) ∂μ
  have hmean : |m - Real.pi * radius ^ 2| ≤ 256 := by
    dsimp [m,μ]
    rw [jitter_count_expectation_eq_midpointGridArea L q hL hq center hr]
    exact midpointGridArea_error_le hR hqR hr hrR
  have hsub : {ω | 30 * Real.sqrt (R * Real.log R) + 256 ≤
        discrepancy (periodicGridSet L q hL hq ω) center radius} ⊆
      {ω | 30 * Real.sqrt (R * Real.log R) ≤
        |(pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) - m|} := by
    intro ω hω
    change 30 * Real.sqrt (R * Real.log R) + 256 ≤
      |(pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) - Real.pi * radius ^ 2| at hω
    have htri := abs_sub_le
      (pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) m (Real.pi * radius ^ 2)
    change 30 * Real.sqrt (R * Real.log R) ≤ _
    linarith
  exact (measureReal_mono hsub).trans (jitter_count_tail L q hL hq center hR hr hrR hperiod)

end DiskDiscrepancy
