import MerLeanExperiment.PeriodicCount
import MerLeanExperiment.InjectiveProductTail

namespace DiskDiscrepancy

noncomputable section

def cellCandidate (q : ℕ) (hq : 0 < q) (z : ℤ × ℤ) (v : Fin q × Fin q) : Plane :=
  periodicGridPoint 1 q (by decide) hq (fun _ ↦ v) z

def cellHit (q : ℕ) (hq : 0 < q) (center : Plane) (radius : ℝ)
    (z : ℤ × ℤ) (v : Fin q × Fin q) : ℝ :=
  if dist (cellCandidate q hq z v) center ≤ radius then 1 else 0

theorem periodicGridPoint_eq_cellCandidate (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (omega : (Fin L × Fin L) → (Fin q × Fin q)) (z : ℤ × ℤ) :
    periodicGridPoint L q hL hq omega z =
      cellCandidate q hq z (omega (intResidue L hL z.1, intResidue L hL z.2)) := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [periodicGridPoint, cellCandidate, jitterPoint, midpointOffset]

theorem cellCandidate_mem_unitCell (q : ℕ) (hq : 0 < q)
    (z : ℤ × ℤ) (v : Fin q × Fin q) : cellCandidate q hq z v ∈ unitCell z :=
  periodicGridPoint_mem_unitCell 1 q (by decide) hq (fun _ ↦ v) z

theorem cellHit_mem_Icc (q : ℕ) (hq : 0 < q) (center : Plane) (radius : ℝ)
    (z : ℤ × ℤ) (v : Fin q × Fin q) :
    0 ≤ cellHit q hq center radius z v ∧ cellHit q hq center radius z v ≤ 1 := by
  unfold cellHit
  split <;> norm_num

theorem cellHit_eq_one_of_meeting_not_boundary (q : ℕ) (hq : 0 < q)
    {center : Plane} {radius : ℝ} {z : ℤ × ℤ}
    (hmeet : MeetingCell center radius z) (hnot : ¬ BoundaryCell center radius z)
    (v : Fin q × Fin q) : cellHit q hq center radius z v = 1 := by
  have hinside : cellCandidate q hq z v ∈ Metric.closedBall center radius := by
    by_contra hout
    apply hnot
    exact ⟨hmeet, cellCandidate q hq z v, cellCandidate_mem_unitCell q hq z v, hout⟩
  have hd : dist (cellCandidate q hq z v) center ≤ radius := hinside
  simp [cellHit, hd]

end

end DiskDiscrepancy
