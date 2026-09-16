import MerLeanExperiment.ExponentialExceptionalMeasure
import MerLeanExperiment.ExponentialSignBridge

open Set

namespace Erdos492Real

noncomputable section

private theorem exponentialMidpoint_eq_cellMidpoint (q j : ℕ) :
    exponentialMidpoint q j = exponentialCellMidpoint q j := by
  rw [exponentialMidpoint, exponentialCellMidpoint]
  ring

/-- Outside the concrete exceptional set, the logarithmic phase is separated
from both integral boundaries and from the arithmetic-midpoint threshold. -/
theorem exponentialExceptionalSet_safe (q : ℕ) (hq : 0 < q) {δ x : ℝ}
    (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hxE : x ∉ exponentialExceptionalSet q δ) :
    exponentialGridPoint q 0 < x ∧
      δ ≤ Int.fract ((q : ℝ) * Real.log x) ∧
      Int.fract ((q : ℝ) * Real.log x) ≤ 1 - δ ∧
      δ ≤ |Int.fract ((q : ℝ) * Real.log x) - phaseThreshold q| := by
  have hbottom : exponentialGridPoint q 0 < x := by
    rw [exponentialGridPoint]
    by_contra h
    apply hxE
    left
    left
    exact ⟨hx0, by simpa using le_of_not_gt h⟩
  obtain ⟨j, hj, hjx, hxj⟩ := exists_exponential_cell q hq hbottom.le hx1
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have ht0 : 0 < δ / (q : ℝ) := div_pos hδ0 hqr
  have hxpos : 0 < x := (Real.exp_pos _).trans hbottom
  have hgpos (i : ℕ) : 0 < exponentialGridPoint q i := by
    rw [exponentialGridPoint]
    exact Real.exp_pos _
  have hcancel : (q : ℝ) * (δ / q) = δ := by field_simp
  have hfract := fract_scaledLog_of_mem_exponentialCell q j hq hjx hxj
  have hnotEndpoint (i : ℕ) (hi : i < q ^ 2 + 1) :
      x ∉ multiplicativeWindow (exponentialGridPoint q i) (δ / q) := by
    intro hx
    apply hxE
    left
    right
    exact Set.mem_iUnion_of_mem i
      (Set.mem_iUnion_of_mem
        (show i ∈ (Finset.range (q ^ 2 + 1) : Set ℕ) from Finset.mem_range.mpr hi) hx)
  have hleftx : exponentialGridPoint q j * Real.exp (δ / q) < x := by
    by_contra h
    apply hnotEndpoint j (by omega)
    constructor
    · calc
        exponentialGridPoint q j * Real.exp (-(δ / q)) ≤ exponentialGridPoint q j := by
          exact mul_le_of_le_one_right (hgpos j).le
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0.le))
        _ ≤ x := hjx
    · exact le_of_not_gt h
  have hrightx : x < exponentialGridPoint q (j + 1) * Real.exp (-(δ / q)) := by
    by_contra h
    apply hnotEndpoint (j + 1) (by omega)
    constructor
    · exact le_of_not_gt h
    · exact (calc
        x < exponentialGridPoint q (j + 1) := hxj
        _ ≤ exponentialGridPoint q (j + 1) * Real.exp (δ / q) := by
          have : 1 ≤ Real.exp (δ / q) := Real.one_le_exp ht0.le
          exact le_mul_of_one_le_right (hgpos (j + 1)).le this).le
  have hphaseLeft :
      (j : ℝ) - q ^ 2 + δ < (q : ℝ) * Real.log x := by
    have hprodpos : 0 < exponentialGridPoint q j * Real.exp (δ / q) :=
      mul_pos (hgpos j) (Real.exp_pos _)
    have hlog := Real.strictMonoOn_log hprodpos hxpos hleftx
    rw [Real.log_mul (hgpos j).ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    have hgrid := scaledLog_exponentialGridPoint q j hq
    nlinarith [hcancel]
  have hphaseRight :
      (q : ℝ) * Real.log x < (j : ℝ) - q ^ 2 + 1 - δ := by
    have hprodpos : 0 < exponentialGridPoint q (j + 1) * Real.exp (-(δ / q)) :=
      mul_pos (hgpos (j + 1)) (Real.exp_pos _)
    have hlog := Real.strictMonoOn_log hxpos hprodpos hrightx
    rw [Real.log_mul (hgpos (j + 1)).ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    have hgrid := scaledLog_exponentialGridPoint q (j + 1) hq
    push_cast at hgrid
    nlinarith [hcancel]
  refine ⟨hbottom, ?_, ?_, ?_⟩
  · rw [hfract]
    linarith
  · rw [hfract]
    linarith
  · have hnotMid :
        x ∉ multiplicativeWindow (exponentialMidpoint q j) (δ / q) := by
      intro hx
      apply hxE
      right
      exact Set.mem_iUnion_of_mem j
        (Set.mem_iUnion_of_mem (show j ∈ (Finset.range (q ^ 2) : Set ℕ) by simpa) hx)
    have hmidpos : 0 < exponentialMidpoint q j := by
      rw [exponentialMidpoint, exponentialGridPoint, exponentialGridPoint]
      positivity
    have hscaledMid := scaledLog_exponentialCellMidpoint q j hq
    rw [← exponentialMidpoint_eq_cellMidpoint] at hscaledMid
    by_cases hxmid : x < exponentialMidpoint q j
    · have hxbelow : x < exponentialMidpoint q j * Real.exp (-(δ / q)) := by
        by_contra h
        apply hnotMid
        exact ⟨le_of_not_gt h, (hxmid.trans_le <| by
          have : 1 ≤ Real.exp (δ / q) := Real.one_le_exp ht0.le
          nlinarith).le⟩
      have hprodpos : 0 < exponentialMidpoint q j * Real.exp (-(δ / q)) := by
        positivity
      have hlog := Real.strictMonoOn_log hxpos hprodpos hxbelow
      rw [Real.log_mul hmidpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
      rw [hfract]
      have hsep : (q : ℝ) * Real.log x - ((j : ℝ) - q ^ 2) - phaseThreshold q ≤ -δ := by
        nlinarith [hcancel]
      rw [abs_of_nonpos (hsep.trans (neg_nonpos.mpr hδ0.le))]
      linarith
    · have hxabove : exponentialMidpoint q j * Real.exp (δ / q) < x := by
        by_contra h
        apply hnotMid
        exact ⟨(by
          have : Real.exp (-(δ / q)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          nlinarith), le_of_not_gt h⟩
      have hprodpos : 0 < exponentialMidpoint q j * Real.exp (δ / q) := by positivity
      have hlog := Real.strictMonoOn_log hprodpos hxpos hxabove
      rw [Real.log_mul hmidpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
      rw [hfract]
      have hsep : δ ≤
          (q : ℝ) * Real.log x - ((j : ℝ) - q ^ 2) - phaseThreshold q := by
        nlinarith [hcancel]
      rw [abs_of_nonneg (hδ0.le.trans hsep)]
      exact hsep

end

end Erdos492Real
