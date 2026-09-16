import MerLeanExperiment.PeriodicLocal
import MerLeanExperiment.BoundaryCells

namespace DiskDiscrepancy

noncomputable section

def relevantCells (center : Plane) (radius : ℝ) : Finset (ℤ × ℤ) :=
  by
    classical
    exact (boundaryCellBox center radius).filter (MeetingCell center radius)

@[simp] theorem mem_relevantCells {center : Plane} {radius : ℝ} (hr : 0 ≤ radius)
    {z : ℤ × ℤ} : z ∈ relevantCells center radius ↔ MeetingCell center radius z := by
  simp only [relevantCells, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦ ⟨meetingCell_mem_boundaryCellBox hr h, h⟩

theorem pointCount_periodicGridSet_eq_sum (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) (center : Plane)
    {radius : ℝ} (hr : 0 ≤ radius) :
    pointCount (periodicGridSet L q hL hq omega) center radius =
      ∑ z ∈ relevantCells center radius,
        if dist (periodicGridPoint L q hL hq omega z) center ≤ radius then 1 else 0 := by
  classical
  let good := (relevantCells center radius).filter fun z ↦
    dist (periodicGridPoint L q hL hq omega z) center ≤ radius
  have hset : diskPoints (periodicGridSet L q hL hq omega) center radius =
      periodicGridPoint L q hL hq omega '' (↑good : Set (ℤ × ℤ)) := by
    ext x
    constructor
    · rintro ⟨⟨z, rfl⟩, hzdist⟩
      have hmeet : MeetingCell center radius z :=
        ⟨periodicGridPoint L q hL hq omega z,
          periodicGridPoint_mem_unitCell L q hL hq omega z, hzdist⟩
      exact ⟨z, by simp [good, mem_relevantCells hr, hmeet, hzdist], rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' := hz
      simp only [good, Finset.mem_coe, Finset.mem_filter] at hz'
      exact ⟨⟨z, rfl⟩, hz'.2⟩
  rw [pointCount, hset]
  unfold periodicGridPoint
  rw [Set.ncard_image_of_injective _
    (jitterPoint_injective (midpointOffset_mem_Ico L q hL hq omega))]
  rw [Set.ncard_coe_finset]
  simp only [good, Finset.sum_boole, periodicGridPoint]
  rfl

end

end DiskDiscrepancy
