import MerLeanExperiment.GridIndexEquiv
import MerLeanExperiment.CellCentered
import MerLeanExperiment.FiniteProductTail

open MeasureTheory Set

namespace DiskDiscrepancy

noncomputable section

noncomputable def cellHitPairs (q : ℕ) (hq : 0 < q) (center : Plane) (radius : ℝ) :
    Finset ((ℤ × ℤ) × (Fin q × Fin q)) := by
  classical
  exact ((relevantCells center radius).product Finset.univ).filter
    (fun p ↦ cellHit q hq center radius p.1 p.2 = 1)

/-- The hit pairs in integer cells map bijectively to the global midpoint-grid
indices in the disk. -/
theorem image_cellHitPairs_gridIndexEquiv {q : ℕ} (hq : 0 < q)
    (center : Plane) {radius : ℝ} (hr : 0 ≤ radius) :
    (cellHitPairs q hq center radius).image (gridIndexEquiv q hq) =
      midpointDiskIndices q center radius := by
  classical
  ext m
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpm⟩
    have hp' := hp
    rw [cellHitPairs, Finset.mem_filter] at hp'
    obtain ⟨hpProd, hpHit⟩ := hp'
    have hpRel := (Finset.mem_product.mp hpProd).1
    apply (mem_midpointDiskIndices hq).2
    have hh : dist (cellCandidate q hq p.1 p.2) center ≤ radius := by
      unfold cellHit at hpHit
      split at hpHit
      · assumption
      · norm_num at hpHit
    rw [← hpm, gridIndexEquiv_apply, ← cellCandidate_eq_gridMidpoint]
    simpa [Metric.mem_closedBall] using hh
  · intro hm
    let p := (gridIndexEquiv q hq).symm m
    have hep : gridIndexEquiv q hq p = m := (gridIndexEquiv q hq).apply_symm_apply m
    have hmid : gridMidpoint q m ∈ Metric.closedBall center radius :=
      (mem_midpointDiskIndices hq).1 hm
    have hcand : cellCandidate q hq p.1 p.2 ∈ Metric.closedBall center radius := by
      have heq : cellCandidate q hq p.1 p.2 = gridMidpoint q m := by
        calc
          cellCandidate q hq p.1 p.2 = gridMidpoint q (gridIndex q p.1 p.2) :=
            cellCandidate_eq_gridMidpoint q hq p.1 p.2
          _ = gridMidpoint q (gridIndexEquiv q hq p) := by
            rw [gridIndexEquiv_apply]
          _ = gridMidpoint q m := congrArg (gridMidpoint q) hep
      rw [heq]
      exact hmid
    have hmeet : MeetingCell center radius p.1 :=
      ⟨cellCandidate q hq p.1 p.2, cellCandidate_mem_unitCell q hq p.1 p.2, hcand⟩
    refine ⟨p, ?_, hep⟩
    rw [cellHitPairs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨(mem_relevantCells hr).2 hmeet,
      Finset.mem_univ _⟩, ?_⟩
    unfold cellHit
    simp [show dist (cellCandidate q hq p.1 p.2) center ≤ radius by
      simpa [Metric.mem_closedBall] using hcand]

 theorem cellHitPairs_card_eq_midpointDiskIndices_card {q : ℕ} (hq : 0 < q)
    (center : Plane) {radius : ℝ} (hr : 0 ≤ radius) :
    (cellHitPairs q hq center radius).card =
      (midpointDiskIndices q center radius).card := by
  rw [← image_cellHitPairs_gridIndexEquiv hq center hr,
    Finset.card_image_of_injective _ (gridIndexEquiv q hq).injective]

/-- Summing every candidate hit over relevant integer cells counts exactly the
finite global midpoint grid in the disk. -/
theorem sum_cellHit_eq_midpointDiskIndices_card {q : ℕ} (hq : 0 < q)
    (center : Plane) {radius : ℝ} (hr : 0 ≤ radius) :
    (∑ z ∈ relevantCells center radius, ∑ v : Fin q × Fin q,
      cellHit q hq center radius z v) =
      ((midpointDiskIndices q center radius).card : ℝ) := by
  rw [← cellHitPairs_card_eq_midpointDiskIndices_card hq center hr]
  classical
  change (∑ z ∈ relevantCells center radius, ∑ v : Fin q × Fin q,
    (if dist (cellCandidate q hq z v) center ≤ radius then 1 else 0)) = _
  norm_cast
  unfold cellHitPairs
  generalize relevantCells center radius = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      let A : Finset ((ℤ × ℤ) × (Fin q × Fin q)) :=
        (Finset.univ.filter fun v ↦ cellHit q hq center radius a v = 1).map
          (Function.Embedding.sectR a (Fin q × Fin q))
      let B : Finset ((ℤ × ℤ) × (Fin q × Fin q)) :=
        (s.product Finset.univ).filter fun p ↦
          cellHit q hq center radius p.1 p.2 = 1
      have hdecomp : ((insert a s).product Finset.univ).filter (fun p ↦
          cellHit q hq center radius p.1 p.2 = 1) = A ∪ B := by
        ext p
        simp [A, B, cellHit]
        aesop
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro p hpA hpB
        rcases Finset.mem_map.mp hpA with ⟨v, _, rfl⟩
        have hps : a ∈ s := (Finset.mem_product.mp (Finset.mem_filter.mp hpB).1).1
        exact ha hps
      rw [hdecomp, Finset.card_union_of_disjoint hdisj]
      rw [Finset.sum_insert ha]
      rw [ih]
      simp [A, B, cellHit]

noncomputable def cellProductMeasure (L q : ℕ) (hq : 0 < q) :
    Measure ((Fin L × Fin L) → (Fin q × Fin q)) := by
  letI : Nonempty (Fin q × Fin q) := ⟨⟨⟨0, hq⟩, ⟨0, hq⟩⟩⟩
  exact Measure.pi (fun _ : Fin L × Fin L ↦
    (PMF.uniformOfFintype (Fin q × Fin q)).toMeasure)

/-- The sum of the actual uniform coordinate expectations is the midpoint-grid
area, with no expectation-to-area assumption. -/
theorem sum_cellHit_expectation_eq_midpointGridArea
    (L q : ℕ) (hL : 0 < L) (hq : 0 < q) (center : Plane)
    {radius : ℝ} (hr : 0 ≤ radius) :
    let μ := cellProductMeasure L q hq
    (∑ z ∈ relevantCells center radius,
      ∫ omega : (Fin L × Fin L) → (Fin q × Fin q),
        cellHit q hq center radius z
          (omega (intResidue L hL z.1, intResidue L hL z.2)) ∂μ) =
      midpointGridArea q center radius := by
  dsimp only
  let _ : Nonempty (Fin q × Fin q) :=
    ⟨⟨⟨0, hq⟩, ⟨0, hq⟩⟩⟩
  have hcard : Fintype.card (Fin q × Fin q) = q ^ 2 := by
    simp
    ring
  rw [show cellProductMeasure L q hq = Measure.pi (fun _ : Fin L × Fin L ↦
      (PMF.uniformOfFintype (Fin q × Fin q)).toMeasure) by
    unfold cellProductMeasure
    rfl]
  simp_rw [uniformProduct_coordinate_expectation]
  simp only [hcard]
  rw [show (∑ z ∈ relevantCells center radius,
      ∑ v : Fin q × Fin q, (↑(q ^ 2))⁻¹ * cellHit q hq center radius z v) =
      (↑(q ^ 2))⁻¹ * ∑ z ∈ relevantCells center radius,
        ∑ v : Fin q × Fin q, cellHit q hq center radius z v by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum]]
  rw [sum_cellHit_eq_midpointDiskIndices_card hq center hr]
  unfold midpointGridArea
  norm_num
  field_simp

end
end DiskDiscrepancy
