import MerLeanExperiment.CellRandom

namespace DiskDiscrepancy

noncomputable section

theorem pointCount_periodicGridSet_real_eq_sum_cellHit
    (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) (center : Plane)
    {radius : ℝ} (hr : 0 ≤ radius) :
    (pointCount (periodicGridSet L q hL hq omega) center radius : ℝ) =
      ∑ z ∈ relevantCells center radius,
        cellHit q hq center radius z
          (omega (intResidue L hL z.1, intResidue L hL z.2)) := by
  rw [pointCount_periodicGridSet_eq_sum L q hL hq omega center hr]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro z hz
  rw [periodicGridPoint_eq_cellCandidate]
  rfl

theorem boundaryCells_subset_relevantCells {center : Plane} {radius : ℝ}
    (hr : 0 ≤ radius) : boundaryCells center radius ⊆ relevantCells center radius := by
  intro z hz
  apply (mem_relevantCells hr).2
  exact ((mem_boundaryCells hr).1 hz).1

end

end DiskDiscrepancy
