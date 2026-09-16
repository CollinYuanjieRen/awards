import MerLeanExperiment.GridRatio
import MerLeanExperiment.GridSums
import Mathlib.Tactic

namespace Erdos441

theorem grid_weights_nonneg (q : ℝ) (hq : 1 < q) (L : ℕ) :
    (∀ i : ℤ, 0 ≤ gridBeta q L i) ∧ ∀ j : ℤ, 0 ≤ gridDelta q L j := by
  have hqp : 0 < q := by linarith
  have hqm : 0 ≤ q - 1 := by linarith
  have heta : 0 < gridEta := (grid_ratio_spec 1 le_rfl).2.2.2
  constructor
  · intro i
    unfold gridBeta
    split_ifs <;> positivity
  · intro j
    unfold gridDelta
    split_ifs with hj0 hjL hjLeq
    · exact mul_nonneg (zpow_pos hqp _).le hqm
    · exact mul_nonneg (div_nonneg hqm (by norm_num))
        (sub_nonneg.mpr (zpow_le_zpow_right₀ hq.le (by omega)))
    · have hh : q ^ (-1 : ℤ) ≤ q ^ (0 : ℤ) :=
        zpow_le_zpow_right₀ hq.le (by norm_num)
      exact sub_nonneg.mpr (by simpa only [zpow_zero] using hh)
    · rfl

theorem grid_delta_sum (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hqL : q ^ (L : ℤ) = Real.sqrt 2) (T : ℤ) (hT : 0 ≤ T) :
    (∑ j ∈ Finset.Icc (-T) (L : ℤ), gridDelta q L j) =
      3 * Real.sqrt 2 / 4 - q ^ (-T) + 1 - q ^ (-1 : ℤ) := by
  classical
  have hqp : 0 < q := by linarith
  have hqne : q ≠ 0 := hqp.ne'
  have hsplit : Finset.Icc (-T) (L : ℤ) =
      (Finset.Icc (-T) (-1) ∪ Finset.Icc 0 ((L : ℤ) - 1)) ∪ {(L : ℤ)} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdis1 : Disjoint (Finset.Icc (-T) (-1)) (Finset.Icc 0 ((L : ℤ) - 1)) := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_Icc] at hj hk
    omega
  have hdis2 : Disjoint (Finset.Icc (-T) (-1) ∪ Finset.Icc 0 ((L : ℤ) - 1))
      {(L : ℤ)} := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at hj hk
    omega
  have hneg : (∑ j ∈ Finset.Icc (-T) (-1), gridDelta q L j) = 1 - q ^ (-T) := by
    calc
      _ = ∑ j ∈ Finset.Icc (-T) (-1), q ^ j * (q - 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [gridDelta, show j < 0 by have := (Finset.mem_Icc.mp hj).2; omega,
          ↓reduceIte]
      _ = _ := by
        rw [sum_Icc_zpow_mul_sub_one q hqne (-T) (-1) (by omega)]
        norm_num
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv : q ^ (-(L : ℤ)) = Real.sqrt 2 / 2 := by
    rw [zpow_neg, hqL]
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
    have hh : (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1 := inv_mul_cancel₀ hspos.ne'
    nlinarith
  have hpos : (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), gridDelta q L j) =
      3 * Real.sqrt 2 / 4 - 1 := by
    calc
      _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (q - 1) * (q ^ j - q ^ (-j - 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 := (Finset.mem_Icc.mp hj).1
        have hjL := (Finset.mem_Icc.mp hj).2
        simp only [gridDelta, not_lt.mpr hj0, show j < (L : ℤ) by omega, ↓reduceIte]
        ring
      _ = _ := by
        rw [sum_Icc_zpow_difference q hqne 0 ((L : ℤ) - 1) (by omega)]
        rw [show (L : ℤ) - 1 + 1 = (L : ℤ) by omega,
          show -((L : ℤ) - 1) - 1 = -(L : ℤ) by omega, hqL, hinv]
        norm_num
        ring
  have hlast : gridDelta q L (L : ℤ) = 1 - q ^ (-1 : ℤ) := by
    simp [gridDelta]
  rw [hsplit, Finset.sum_union hdis2, Finset.sum_union hdis1, Finset.sum_singleton,
    hneg, hpos, hlast]
  ring

end Erdos441

#print axioms Erdos441.grid_weights_nonneg
#print axioms Erdos441.grid_delta_sum
