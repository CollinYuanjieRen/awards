import MerLeanExperiment.CellCentered

open MeasureTheory

namespace DiskDiscrepancy

theorem integrable_sampled_cellHit (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (center : Plane) (radius : ℝ) (z : ℤ × ℤ)
    (μ : Measure ((Fin L × Fin L) → (Fin q × Fin q))) [IsFiniteMeasure μ] :
    Integrable (fun ω ↦ cellHit q hq center radius z
      (ω (intResidue L hL z.1, intResidue L hL z.2))) μ := by
  apply Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable 1
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (cellHit_mem_Icc q hq center radius z _).1]
  exact (cellHit_mem_Icc q hq center radius z _).2

/-- In the actual point count, only cells crossing the disk boundary fluctuate around expectation. -/
theorem centered_count_eq_boundary_sum (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (center : Plane) {radius : ℝ} (hr : 0 ≤ radius)
    (μ : Measure ((Fin L × Fin L) → (Fin q × Fin q))) [IsProbabilityMeasure μ]
    (ω : (Fin L × Fin L) → (Fin q × Fin q)) :
    (pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) -
      (∫ ω', (pointCount (periodicGridSet L q hL hq ω') center radius : ℝ) ∂μ) =
    ∑ z ∈ boundaryCells center radius,
      (cellHit q hq center radius z (ω (intResidue L hL z.1, intResidue L hL z.2)) -
        ∫ ω', cellHit q hq center radius z (ω' (intResidue L hL z.1, intResidue L hL z.2)) ∂μ) := by
  classical
  simp_rw [pointCount_periodicGridSet_real_eq_sum_cellHit L q hL hq _ center hr]
  rw [integral_finsetSum _ (fun z _ ↦ integrable_sampled_cellHit L q hL hq center radius z μ),
    ← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (boundaryCells_subset_relevantCells hr)
  intro z hz hznot
  have hm : MeetingCell center radius z := (mem_relevantCells hr).mp hz
  have hb : ¬BoundaryCell center radius z := by simpa only [mem_boundaryCells hr] using hznot
  have hconst (ω' : (Fin L × Fin L) → (Fin q × Fin q)) :
      cellHit q hq center radius z (ω' (intResidue L hL z.1, intResidue L hL z.2)) = 1 :=
    cellHit_eq_one_of_meeting_not_boundary q hq hm hb _
  simp [hconst]

end DiskDiscrepancy
