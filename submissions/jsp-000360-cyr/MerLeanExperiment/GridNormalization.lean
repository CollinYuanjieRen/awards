import MerLeanExperiment.IntervalCounts
import MerLeanExperiment.GridWeightSums
import Mathlib.Tactic

namespace Erdos441

open scoped BigOperators

/-- The unweighted count of the middle geometric range is bounded by its
weighted density sum. -/
theorem grid_middle_le_weighted_density (A : Finset ℕ) (q : ℝ) (hq : 1 < q)
    (L : ℕ) (T : ℤ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) / R ≤
      ∑ i ∈ Finset.Icc (-T) T,
        gridBeta q L i * intervalDensity A (q ^ i) (q ^ (i + 1)) R := by
  classical
  have hq0 : 0 < q := by linarith
  have heta : 0 ≤ gridEta := (grid_ratio_spec 1 le_rfl).2.2.2.le
  have hwidth (i : ℤ) : q ^ (i + 1) - q ^ i = q ^ i * (q - 1) := by
    rw [zpow_add_one₀ hq0.ne']
    ring
  have hwidth_pos (i : ℤ) : 0 < q ^ i * (q - 1) :=
    mul_pos (zpow_pos hq0 i) (sub_pos.mpr hq)
  have hdensity (i : ℤ) :
      intervalDensity A (q ^ i) (q ^ (i + 1)) R =
        ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) /
          ((q ^ i * (q - 1)) * R) := by
    unfold intervalDensity intervalRegion
    rw [hwidth]
  have hcancel (i : ℤ) :
      (q ^ i * (q - 1)) * intervalDensity A (q ^ i) (q ^ (i + 1)) R =
        ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R := by
    rw [hdensity]
    field_simp [hq0.ne', (sub_pos.mpr hq).ne', hR.ne']
  have hrow (i : ℤ) :
      ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R ≤
        gridBeta q L i * intervalDensity A (q ^ i) (q ^ (i + 1)) R := by
    by_cases hi : i < (L : ℤ)
    · rw [gridBeta, if_pos hi, hcancel]
    · rw [gridBeta, if_neg hi]
      have hc : 0 ≤ ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R :=
        div_nonneg (Nat.cast_nonneg _) hR.le
      calc
        ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R ≤
            (1 + gridEta) *
              (((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R) := by
                nlinarith [mul_nonneg heta hc]
        _ = (1 + gridEta) * q ^ i * (q - 1) *
              intervalDensity A (q ^ i) (q ^ (i + 1)) R := by
                rw [← hcancel i]
                ring
  calc
    ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) / R =
        (∑ i ∈ Finset.Icc (-T) T,
          ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ)) / R := by
            rw [grid_middle_card_sum A q hq T hT R hR.le]
    _ = ∑ i ∈ Finset.Icc (-T) T,
          ((intervalRegion A (q ^ i) (q ^ (i + 1)) R).card : ℝ) / R := by
            rw [Finset.sum_div]
    _ ≤ ∑ i ∈ Finset.Icc (-T) T,
          gridBeta q L i * intervalDensity A (q ^ i) (q ^ (i + 1)) R := by
            exact Finset.sum_le_sum fun i _ ↦ hrow i

/-- The geometric scale identity iterates over a natural block count. -/
theorem grid_scale_power (q : ℝ) (L S : ℕ)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) :
    q ^ (2 * (L : ℤ) * (S : ℤ)) = (2 : ℝ) ^ S := by
  rw [zpow_mul, hq2L, zpow_natCast]

/-- The square-root constant used at the endpoint of the grid estimate. -/
theorem sqrt_nine_eighth :
    Real.sqrt (9 / 8 : ℝ) = 3 * Real.sqrt 2 / 4 := by
  have hleft : 0 ≤ Real.sqrt (9 / 8 : ℝ) := Real.sqrt_nonneg _
  have hright : 0 ≤ 3 * Real.sqrt 2 / 4 := by positivity
  have hleft_sq : (Real.sqrt (9 / 8 : ℝ)) ^ 2 = 9 / 8 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

end Erdos441

#print axioms Erdos441.grid_middle_le_weighted_density
#print axioms Erdos441.grid_scale_power
#print axioms Erdos441.sqrt_nine_eighth
