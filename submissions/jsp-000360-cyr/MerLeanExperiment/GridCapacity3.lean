import MerLeanExperiment.GridPrefixIdentity
import MerLeanExperiment.GridSums
import MerLeanExperiment.GridScalarDefinitions
import Mathlib.Tactic

namespace Erdos441

open scoped BigOperators

private lemma grid_neg_one_mem_case3 (q : ℝ) (hq : 1 < q) (L : ℕ)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) (t j : ℤ)
    (hjlo : -t ≤ j) (hjhi : j ≤ t - 2 * (L : ℤ)) :
    (-1 : ℤ) ∈ gridA q t j := by
  have hqpos : 0 < q := by linarith
  have hjt : j ≤ t := by omega
  simp only [gridA, hjt, ↓reduceIte, mem_gridPoints]
  right
  have hprod : 1 ≤ q ^ j * q ^ t := by
    rw [← zpow_add₀ hqpos.ne']
    exact one_le_zpow₀ hq.le (by omega)
  have hratio : 2 ≤ q ^ t / q ^ j := by
    rw [← zpow_sub₀ hqpos.ne']
    rw [← hq2L]
    exact zpow_le_zpow_right₀ hq.le (by omega)
  have hmin : 1 ≤ min (q ^ j * q ^ t) (q ^ t / q ^ j - 1) :=
    le_min hprod (by linarith)
  constructor
  · norm_num
    exact ⟨hprod, by linarith⟩
  · norm_num

private lemma grid_two_mem_case3 (q : ℝ) (hq : 1 < q) (L : ℕ)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) (t j : ℤ)
    (hjt : j ≤ t) (hsum : 2 * (L : ℤ) ≤ j + t) :
    (2 : ℤ) ∈ gridA q t j := by
  have hqpos : 0 < q := by linarith
  simp only [gridA, hjt, ↓reduceIte, mem_gridPoints]
  left
  constructor
  · norm_num
  · have hp : (2 : ℝ) ≤ q ^ (j + t) := by
      rw [← hq2L]
      exact zpow_le_zpow_right₀ hq.le hsum
    rw [zpow_add₀ hqpos.ne'] at hp
    exact_mod_cast hp

private lemma grid_neg_weight_nonneg (q : ℝ) (hq : 1 < q) (j : ℤ) :
    0 ≤ q ^ j * (q - 1) := by positivity

private lemma grid_pos_weight_nonneg (q : ℝ) (hq : 1 < q) (j : ℤ) (hj : 0 ≤ j) :
    0 ≤ (q - 1) * (q ^ j - q ^ (-j - 1)) := by
  have hp := zpow_le_zpow_right₀ hq.le (show -j - 1 ≤ j by omega)
  exact mul_nonneg (by linarith) (sub_nonneg.mpr hp)

/-- The five actual grid-column blocks in Case 3 give precisely the source
residual lower bound; all cardinality estimates come from concrete members. -/
theorem grid_case3_capacity (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hqL : q ^ (L : ℤ) = Real.sqrt 2) (hq2L : q ^ (2 * (L : ℤ)) = 2)
    (T t : ℤ) (hT : 0 ≤ T) (htT : t ≤ T) (hLt : (L : ℤ) ≤ t)
    (ht2L : t < 2 * (L : ℤ)) :
    gridBetaPrefix q L T t + gridResidual3 q (q ^ t) ≤
      gridCapacityPrefix q L T t := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := hqpos.ne'
  have ht0 : 0 ≤ t := by omega
  have htlo : -T ≤ t := by omega
  rw [grid_capacity_prefix_eq q hq L hL T t hT htlo]
  rw [ite_eq_left ht0]
  let wn : ℤ → ℝ := fun j ↦ q ^ j * (q - 1)
  let wp : ℤ → ℝ := fun j ↦ (q - 1) * (q ^ j - q ^ (-j - 1))
  let h : ℤ := 2 * (L : ℤ) - t
  have hh1 : 1 ≤ h := by omega
  have hhL : h ≤ (L : ℤ) := by omega
  have hneg :
      ( (∑ j ∈ Finset.Icc (-T) (-1), wn j) +
          ∑ j ∈ Finset.Icc (-t) (-1), wn j) +
          ∑ j ∈ Finset.Icc (-t) (t - 2 * (L : ℤ)), wn j ≤
        ∑ j ∈ Finset.Icc (-T) (-1),
          (gridA q t j).card * q ^ j * (q - 1) := by
    have hsumA :
        (∑ j ∈ Finset.Icc (-T) (-1), if -t ≤ j then wn j else 0) =
          ∑ j ∈ Finset.Icc (-t) (-1), wn j := by
      have hf : (Finset.Icc (-T) (-1)).filter (fun j ↦ -t ≤ j) =
          Finset.Icc (-t) (-1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [← hf, Finset.sum_filter]
    have hsumB :
        (∑ j ∈ Finset.Icc (-T) (-1),
          if -t ≤ j ∧ j ≤ t - 2 * (L : ℤ) then wn j else 0) =
          ∑ j ∈ Finset.Icc (-t) (t - 2 * (L : ℤ)), wn j := by
      have hf : (Finset.Icc (-T) (-1)).filter
          (fun j ↦ -t ≤ j ∧ j ≤ t - 2 * (L : ℤ)) =
          Finset.Icc (-t) (t - 2 * (L : ℤ)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [← hf, Finset.sum_filter]
    have heq :
        ((∑ j ∈ Finset.Icc (-T) (-1), wn j) +
            ∑ j ∈ Finset.Icc (-t) (-1), wn j) +
            ∑ j ∈ Finset.Icc (-t) (t - 2 * (L : ℤ)), wn j =
          ∑ j ∈ Finset.Icc (-T) (-1),
            ((wn j + if -t ≤ j then wn j else 0) +
              if -t ≤ j ∧ j ≤ t - 2 * (L : ℤ) then wn j else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumA, hsumB]
    rw [heq]
    apply Finset.sum_le_sum
    intro j hjmem
    have hjr := Finset.mem_Icc.mp hjmem
    have hjt : j ≤ t := by omega
    have hw := grid_neg_weight_nonneg q hq j
    by_cases ha : -t ≤ j
    · by_cases hb : j ≤ t - 2 * (L : ℤ)
      · have hsub : ({-1, 0, 1} : Finset ℤ) ⊆ gridA q t j := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact grid_neg_one_mem_case3 q hq L hq2L t j ha hb
          · exact zero_mem_grid_column q hq t j hjt
          · exact (zero_one_subset_grid_column q hq t j hjt (by omega)) (by simp)
        have hcN : 3 ≤ (gridA q t j).card := by
          have hc := Finset.card_le_card hsub
          norm_num at hc ⊢
          exact hc
        have hc : (3 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
        simp [ha, hb, wn]
        nlinarith
      · have hcN : 2 ≤ (gridA q t j).card :=
          Finset.card_le_card (zero_one_subset_grid_column q hq t j hjt (by omega))
        have hc : (2 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
        simp [ha, hb, wn]
        nlinarith
    · have hcN : 1 ≤ (gridA q t j).card :=
        Finset.one_le_card.mpr ⟨0, zero_mem_grid_column q hq t j hjt⟩
      have hc : (1 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
      simp [ha, wn]
      nlinarith
  have hpos :
      (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), wp j) +
          (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc h ((L : ℤ) - 1), wp j) ≤
        (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)) := by
    have hsumH :
        (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), if h ≤ j then wp j else 0) =
          ∑ j ∈ Finset.Icc h ((L : ℤ) - 1), wp j := by
      have hf : (Finset.Icc 0 ((L : ℤ) - 1)).filter (fun j ↦ h ≤ j) =
          Finset.Icc h ((L : ℤ) - 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [← hf, Finset.sum_filter]
    have heq :
        (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), wp j) +
            (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc h ((L : ℤ) - 1), wp j) =
          ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
            ((1 / 2 : ℝ) * (2 * wp j + if h ≤ j then wp j else 0)) := by
      rw [← hsumH, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split <;> ring
    rw [heq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hjmem
    have hjr := Finset.mem_Icc.mp hjmem
    have hjt : j ≤ t := by omega
    have hw := grid_pos_weight_nonneg q hq j hjr.1
    by_cases hjh : h ≤ j
    · have hsub : ({0, 1, 2} : Finset ℤ) ⊆ gridA q t j := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact zero_mem_grid_column q hq t j hjt
        · exact (zero_one_subset_grid_column q hq t j hjt (by omega)) (by simp)
        · exact grid_two_mem_case3 q hq L hq2L t j hjt (by dsimp [h] at hjh; omega)
      have hcN : 3 ≤ (gridA q t j).card := by
        have hc := Finset.card_le_card hsub
        norm_num at hc ⊢
        exact hc
      have hc : (3 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
      simp [hjh, wp]
      nlinarith
    · have hcN : 2 ≤ (gridA q t j).card :=
        Finset.card_le_card (zero_one_subset_grid_column q hq t j hjt (by omega))
      have hc : (2 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast hcN
      simp [hjh, wp]
      nlinarith
  have hs1 := sum_Icc_zpow_mul_sub_one q hqne (-T) (-1) (by omega)
  have hs2 := sum_Icc_zpow_mul_sub_one q hqne (-t) (-1) (by omega)
  have hs3 := sum_Icc_zpow_mul_sub_one q hqne (-t) (t - 2 * (L : ℤ)) (by omega)
  have hp1 := sum_Icc_zpow_difference q hqne 0 ((L : ℤ) - 1) (by omega)
  have hp2 := sum_Icc_zpow_difference q hqne h ((L : ℤ) - 1) (by omega)
  have hlower := add_le_add (add_le_add hneg hpos) (le_refl (1 - q ^ (-1 : ℤ)))
  have hqtpos : 0 < q ^ t := zpow_pos hqpos t
  have ht1 : q ^ (t + 1) = q ^ t * q := by rw [zpow_add_one₀ hqne]
  have hnt : q ^ (-t) = 1 / q ^ t := by simp [zpow_neg, one_div]
  have hnL : q ^ (-(L : ℤ)) = 1 / q ^ (L : ℤ) := by
    simp [zpow_neg, one_div]
  have hhpow : q ^ h = 2 / q ^ t := by
    dsimp [h]
    rw [zpow_sub₀ hqne, hq2L]
  have hhneg : q ^ (-h) = q ^ t / 2 := by
    rw [zpow_neg, hhpow]
    field_simp [hqtpos.ne']
  have hthird : q ^ (t - 2 * (L : ℤ) + 1) = q ^ t * q / 2 := by
    have he : t - 2 * (L : ℤ) + 1 = (t + 1) - 2 * (L : ℤ) := by omega
    rw [he, zpow_sub₀ hqne, hq2L, ht1]
  have hLp : (L : ℤ) - 1 + 1 = (L : ℤ) := by omega
  have hLm : -((L : ℤ) - 1) - 1 = -(L : ℤ) := by omega
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsInv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp [hspos.ne']
    nlinarith [hsSq]
  have hnegone : q ^ (-1 : ℤ) = 1 / q := by
    rw [zpow_neg]
    norm_num [one_div]
  have htarget :
      gridBetaPrefix q L T t + gridResidual3 q (q ^ t) =
        (((∑ j ∈ Finset.Icc (-T) (-1), wn j) +
            ∑ j ∈ Finset.Icc (-t) (-1), wn j) +
            ∑ j ∈ Finset.Icc (-t) (t - 2 * (L : ℤ)), wn j) +
          ((∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), wp j) +
            (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc h ((L : ℤ) - 1), wp j)) +
          (1 - q ^ (-1 : ℤ)) := by
    rw [grid_beta_prefix_eq q hqne L T t hT hLt]
    dsimp [wn, wp]
    rw [hs1, hs2, hs3, hp1, hp2]
    norm_num only [Int.reduceNeg, add_neg_cancel, zpow_zero]
    rw [hLp, hLm, ht1, hnt, hnL, hhpow, hhneg, hthird, hqL, hnegone, hsInv]
    dsimp [gridResidual3, gridEta]
    field_simp [hqne, hqtpos.ne', hspos.ne']
    ring_nf
  rw [htarget]
  exact hlower

end Erdos441
