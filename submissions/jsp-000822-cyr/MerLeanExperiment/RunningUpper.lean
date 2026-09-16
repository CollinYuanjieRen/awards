import MerLeanExperiment.JitterDiscrepancy
import MerLeanExperiment.NetExistence
import MerLeanExperiment.Target
import Mathlib.Analysis.Complex.ExponentialBounds

namespace DiskDiscrepancy

/-- One actual infinite periodic point set controls all centers and all tested radii at each scale. -/
theorem runningUpper : RunningUpperBound := by
  refine ⟨1000, by norm_num, 4, by norm_num, ?_⟩
  intro R hR
  obtain ⟨L,q,K,hL,hq,_hKpos,hperiod,hqR,hK,hcard⟩ := exists_net_parameters hR
  obtain ⟨ω,hω⟩ := exists_periodic_grid_of_tail hL hq hR hqR hK hcard
    (jitterMeasure L q hq) (fun x r hr hrR ↦
      jitter_discrepancy_tail L q hL hq x hR hqR hr.le hrR (by linarith))
  refine ⟨periodicGridSet L q hL hq ω, admissible_periodicGridSet L q hL hq ω, ?_⟩
  intro x r hr hrR
  have h := hω x r hr hrR
  have hR0 : 0 < R := by linarith
  have hlog : 1 ≤ Real.log R := (Real.le_log_iff_exp_le hR0).mpr
    (by linarith [Real.exp_one_lt_three])
  have hprod : 1 ≤ R * Real.log R := by nlinarith
  have hs := Real.sq_sqrt (by linarith : 0 ≤ R * Real.log R)
  have hs0 := Real.sqrt_nonneg (R * Real.log R)
  have hs1 : 1 ≤ Real.sqrt (R * Real.log R) := by nlinarith
  nlinarith [Real.pi_le_four]

end DiskDiscrepancy
