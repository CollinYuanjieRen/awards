import MerLeanExperiment.CellExpectation
import MerLeanExperiment.NetProbability

open MeasureTheory

namespace DiskDiscrepancy

noncomputable def jitterMeasure (L q : ℕ) (hq : 0 < q) :
    Measure ((Fin L × Fin L) → (Fin q × Fin q)) := by
  letI : Nonempty (Fin q × Fin q) := ⟨(⟨0,hq⟩,⟨0,hq⟩)⟩
  exact Measure.pi (fun _ : Fin L × Fin L ↦ (PMF.uniformOfFintype (Fin q × Fin q)).toMeasure)

instance jitterMeasure_probability (L q : ℕ) (hq : 0 < q) :
    IsProbabilityMeasure (jitterMeasure L q hq) := by
  unfold jitterMeasure
  infer_instance

/-- An actual periodic jitter count satisfies the boundary-cell Hoeffding estimate. -/
theorem jitter_count_tail (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (center : Plane) {radius R : ℝ} (hR : 4 ≤ R) (hr : 0 ≤ radius)
    (hrR : radius ≤ R + 1) (hperiod : 2 * radius + 1 < L) :
    (jitterMeasure L q hq).real {ω |
      30 * Real.sqrt (R * Real.log R) ≤
        |(pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) -
          ∫ ω', (pointCount (periodicGridSet L q hL hq ω') center radius : ℝ) ∂jitterMeasure L q hq|}
      ≤ 2 / R ^ 15 := by
  classical
  let μ := jitterMeasure L q hq
  let B := boundaryCells center radius
  let t := 30 * Real.sqrt (R * Real.log R)
  have hR0 : 0 < R := by linarith
  have ht : 0 < t := by
    have hlog : 0 < Real.log R := Real.log_pos (by linarith)
    dsimp [t]
    positivity
  have hidentity := centered_count_eq_boundary_sum L q hL hq center hr μ
  change μ.real {ω | t ≤ |(pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) -
    ∫ ω', (pointCount (periodicGridSet L q hL hq ω') center radius : ℝ) ∂μ|} ≤ _
  by_cases hB : B.Nonempty
  · let J := {z // z ∈ B}
    let g : J → Fin L × Fin L := fun z ↦ (intResidue L hL z.val.1, intResidue L hL z.val.2)
    have hg : Function.Injective g := by
      intro z w heq
      apply Subtype.ext
      exact residue_injective_on_meetingCells hL hperiod
        (((mem_boundaryCells hr).mp z.property).1)
        (((mem_boundaryCells hr).mp w.property).1) heq
    let X : J → (Fin q × Fin q) → ℝ := fun z ↦ cellHit q hq center radius z.val
    let : Nonempty (Fin q × Fin q) := ⟨(⟨0,hq⟩,⟨0,hq⟩)⟩
    have hJ : (Finset.univ : Finset J).Nonempty := by
      obtain ⟨z,hz⟩ := hB
      exact ⟨⟨z,hz⟩,Finset.mem_univ _⟩
    have htail := uniformProduct_injective_centered_sum_tail g hg X
      (fun z v ↦ (cellHit_mem_Icc q hq center radius z.val v).1)
      (fun z v ↦ (cellHit_mem_Icc q hq center radius z.val v).2) Finset.univ hJ ht.le
    change μ.real {ω | t ≤ |∑ z : J, (X z (ω (g z)) - ∫ ω', X z (ω' (g z)) ∂μ)|} ≤
      2 * Real.exp (-2 * t ^ 2 / (Finset.univ : Finset J).card) at htail
    have hsum (ω : (Fin L × Fin L) → (Fin q × Fin q)) :
        (∑ z : J, (X z (ω (g z)) - ∫ ω', X z (ω' (g z)) ∂μ)) =
        (pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) -
          ∫ ω', (pointCount (periodicGridSet L q hL hq ω') center radius : ℝ) ∂μ := by
      rw [hidentity ω]
      exact Finset.sum_coe_sort B (fun z : ℤ × ℤ ↦
        cellHit q hq center radius z (ω (intResidue L hL z.1, intResidue L hL z.2)) -
          ∫ ω', cellHit q hq center radius z (ω' (intResidue L hL z.1, intResidue L hL z.2)) ∂μ)
    simp_rw [hsum] at htail
    have hcard : (Finset.univ : Finset J).card = B.card := by simp [J]
    rw [hcard] at htail
    have hcardpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    exact htail.trans (boundary_tail_numerical hR hcardpos (boundaryCells_card_le hR hr hrR))
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hevent : {ω | t ≤ |(pointCount (periodicGridSet L q hL hq ω) center radius : ℝ) -
        ∫ ω', (pointCount (periodicGridSet L q hL hq ω') center radius : ℝ) ∂μ|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      rw [hidentity ω]
      change (t ≤ |∑ z ∈ B, _|) ↔ False
      simp [he, ht.not_ge]
    rw [hevent, measureReal_empty]
    positivity

end DiskDiscrepancy
