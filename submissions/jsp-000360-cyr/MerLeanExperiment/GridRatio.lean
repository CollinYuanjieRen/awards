import MerLeanExperiment.GridDefinitions
import Mathlib.Analysis.SpecificLimits.Basic

namespace Erdos441

theorem grid_ratio_spec (L : ℕ) (hL : 1 ≤ L) :
    1 < gridQ L ∧ gridQ L ^ (L : ℤ) = Real.sqrt 2 ∧
      gridQ L ^ (2 * (L : ℤ)) = 2 ∧ 0 < gridEta := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hq : 1 < gridQ L := Real.one_lt_rpow (by norm_num) (by positivity)
  have hqL : gridQ L ^ (L : ℤ) = Real.sqrt 2 := by
    rw [gridQ, ← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), Real.sqrt_eq_rpow]
    congr 1
    push_cast
    field_simp
  have hq2L : gridQ L ^ (2 * (L : ℤ)) = 2 := by
    rw [mul_comm (2 : ℤ), zpow_mul, hqL]
    norm_num [Real.sq_sqrt]
  have heta : 0 < gridEta := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    dsimp [gridEta]
    nlinarith
  exact ⟨hq, hqL, hq2L, heta⟩

theorem gridQ_tendsto_one : Filter.Tendsto gridQ Filter.atTop (nhds 1) := by
  have h := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2 / 2)
  have he := Real.continuous_exp.continuousAt.tendsto.comp h
  have hid : gridQ = fun L : ℕ => Real.exp ((Real.log 2 / 2) / (L : ℝ)) := by
    funext L
    rw [gridQ, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid]
  simpa only [Real.exp_zero, Function.comp_def] using he

end Erdos441

#print axioms Erdos441.grid_ratio_spec
#print axioms Erdos441.gridQ_tendsto_one
