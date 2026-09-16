import MerLeanExperiment.GridSums
import Mathlib.Tactic

namespace Erdos441

open scoped BigOperators

private lemma grid_case4_column_card_lower (q : ℝ) (hq : 1 < q) (L : ℕ)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) (t j : ℤ)
    (ht : 2 * (L : ℤ) ≤ t) (hj0 : 0 ≤ j) (hjL : j ≤ (L : ℤ) - 1) :
    q ^ t * (q ^ j + q ^ (-j)) - 2 ≤ ((gridA q t j).card : ℝ) := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := hqpos.ne'
  have hjt : j ≤ t := by omega
  have hαpos : 0 < q ^ j := zpow_pos hqpos j
  have hαβ : q ^ j ≤ q ^ t := zpow_le_zpow_right₀ hq.le hjt
  have hqtpos : 0 < q ^ t := zpow_pos hqpos t
  have hqj_one : 1 ≤ q ^ j := one_le_zpow₀ hq.le hj0
  have hqt_two : (2 : ℝ) ≤ q ^ t := by
    rw [← hq2L]
    exact zpow_le_zpow_right₀ hq.le ht
  have hdiv_le : q ^ t / q ^ j ≤ q ^ t := by
    exact (div_le_iff₀ hαpos).2 (by nlinarith)
  have hmin_le : q ^ t / q ^ j - 1 ≤ q ^ j * q ^ t := by
    nlinarith [mul_le_mul_of_nonneg_right hqj_one hqtpos.le]
  have hmin : min (q ^ j * q ^ t) (q ^ t / q ^ j - 1) = q ^ t / q ^ j - 1 :=
    min_eq_right hmin_le
  have hcZ := grid_points_card (q ^ j) (q ^ t) hαpos hαβ
  have hcR : ((gridPoints (q ^ j) (q ^ t)).card : ℝ) =
      (⌊q ^ j * q ^ t⌋ : ℝ) +
        (⌊min (q ^ j * q ^ t) (q ^ t / q ^ j - 1)⌋ : ℝ) + 1 := by
    exact_mod_cast hcZ
  have hf₁ : q ^ j * q ^ t - 1 ≤ (⌊q ^ j * q ^ t⌋ : ℝ) := by
    have h := Int.lt_floor_add_one (q ^ j * q ^ t)
    linarith
  have hf₂ : q ^ t / q ^ j - 2 ≤ (⌊q ^ t / q ^ j - 1⌋ : ℝ) := by
    have h := Int.lt_floor_add_one (q ^ t / q ^ j - 1)
    linarith
  have hneg : q ^ t / q ^ j = q ^ t * q ^ (-j) := by
    rw [zpow_neg]
    field_simp
  simp only [gridA, hjt, ↓reduceIte]
  rw [hmin] at hcR
  calc
    q ^ t * (q ^ j + q ^ (-j)) - 2 =
        q ^ j * q ^ t + q ^ t / q ^ j - 2 := by rw [hneg]; ring
    _ ≤ ((gridPoints (q ^ j) (q ^ t)).card : ℝ) := by
      rw [hcR]
      linarith

private lemma grid_case4_square_sum (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hq2L : q ^ (2 * (L : ℤ)) = 2) :
    ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1)) =
      (1 - q / 2) / (1 + q) := by
  have hqne : q ≠ 0 := by linarith
  have hden : q ^ 2 - 1 ≠ 0 := by nlinarith
  have htel₁ := sum_Icc_backward_sub
    (fun j : ℤ ↦ q ^ (2 * j + 2)) 0 ((L : ℤ) - 1) (by omega)
  have hs₁ :
      ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (q ^ 2 - 1) * q ^ (2 * j) = 1 := by
    calc
      _ = ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (q ^ (2 * j + 2) - q ^ (2 * (j - 1) + 2)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show 2 * (j - 1) + 2 = 2 * j by omega]
        rw [show q ^ (2 * j + 2) = q ^ (2 * j) * q ^ 2 by
          rw [show 2 * j + 2 = 2 * j + (2 : ℤ) by omega, zpow_add₀ hqne]
          norm_num]
        ring
      _ = q ^ (2 * ((L : ℤ) - 1) + 2) - q ^ (2 * (0 - 1) + 2) := htel₁
      _ = 1 := by
        rw [show 2 * ((L : ℤ) - 1) + 2 = 2 * (L : ℤ) by omega,
          show 2 * ((0 : ℤ) - 1) + 2 = 0 by omega, hq2L]
        norm_num
  have htel₂ := sum_Icc_backward_sub
    (fun j : ℤ ↦ -q ^ (-2 * j - 1)) 0 ((L : ℤ) - 1) (by omega)
  have hs₂ :
      ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (q ^ 2 - 1) * q ^ (-2 * j - 1) = q / 2 := by
    calc
      _ = ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (-q ^ (-2 * j - 1) - (-q ^ (-2 * (j - 1) - 1))) := by
        apply Finset.sum_congr rfl
        intro j _
        have he : -2 * (j - 1) - 1 = -2 * j + 1 := by omega
        rw [he]
        have hp : q ^ (-2 * j + 1) = q ^ (-2 * j - 1) * q ^ 2 := by
          rw [show -2 * j + 1 = (-2 * j - 1) + 2 by omega, zpow_add₀ hqne]
          norm_num
        rw [hp]
        ring
      _ = -q ^ (-2 * ((L : ℤ) - 1) - 1) -
          (-q ^ (-2 * (0 - 1) - 1)) := htel₂
      _ = q / 2 := by
        rw [show -2 * ((L : ℤ) - 1) - 1 = -2 * (L : ℤ) + 1 by omega,
          show -2 * ((0 : ℤ) - 1) - 1 = 1 by omega]
        have hp : q ^ (-2 * (L : ℤ) + 1) = q / 2 := by
          rw [show -2 * (L : ℤ) + 1 = 1 - 2 * (L : ℤ) by omega,
            zpow_sub₀ hqne, hq2L]
          norm_num
        rw [hp, zpow_one]
        ring
  have hsum₁ :
      ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), q ^ (2 * j) = 1 / (q ^ 2 - 1) := by
    apply (eq_div_iff hden).2
    rw [Finset.sum_mul]
    simpa [mul_comm] using hs₁
  have hsum₂ :
      ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), q ^ (-2 * j - 1) =
        (q / 2) / (q ^ 2 - 1) := by
    apply (eq_div_iff hden).2
    rw [Finset.sum_mul]
    simpa [mul_comm] using hs₂
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum₁, hsum₂]
  field_simp
  ring

private lemma grid_case4_summand_expand (q : ℝ) (hq : 1 < q) (t j : ℤ) :
    (q ^ t * (q ^ j + q ^ (-j)) - 2) *
        ((q - 1) * (q ^ j - q ^ (-j - 1))) =
      q ^ t * ((q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1))) +
        (q - 1) * q ^ t * (1 - 1 / q) -
        2 * ((q - 1) * (q ^ j - q ^ (-j - 1))) := by
  have hqne : q ≠ 0 := by linarith
  have hsq : q ^ j * q ^ j = q ^ (2 * j) := by
    rw [← zpow_add₀ hqne]
    congr 1
    omega
  have hone : q ^ j * q ^ (-j) = 1 := by
    rw [← zpow_add₀ hqne]
    norm_num
  have hinv : q ^ j * q ^ (-j - 1) = 1 / q := by
    rw [← zpow_add₀ hqne]
    rw [show j + (-j - 1) = (-1 : ℤ) by omega]
    simp [one_div]
  have href : q ^ (-j - 1) * q ^ (-j) = q ^ (-2 * j - 1) := by
    rw [← zpow_add₀ hqne]
    congr 1
    omega
  calc
    _ = q ^ t * (q - 1) *
          (q ^ j * q ^ j + q ^ j * q ^ (-j) -
            q ^ j * q ^ (-j - 1) - q ^ (-j - 1) * q ^ (-j)) -
        2 * ((q - 1) * (q ^ j - q ^ (-j - 1))) := by ring
    _ = _ := by rw [hsq, hone, hinv, href]; ring

/-- The nonnegative grid columns in Case 4 supply the source's positive-column
lower bound, derived directly from the concrete grid-point cardinalities. -/
theorem grid_case4_positive_columns (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hqL : q ^ (L : ℤ) = Real.sqrt 2)
    (hq2L : q ^ (2 * (L : ℤ)) = 2)
    (t : ℤ) (ht : 2 * (L : ℤ) ≤ t) :
    q ^ t / (2 * (1 + q)) * (1 - q / 2) + 2 - 3 * Real.sqrt 2 / 2 ≤
      (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)) := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := hqpos.ne'
  let I : Finset ℤ := Finset.Icc 0 ((L : ℤ) - 1)
  let W : ℤ → ℝ := fun j ↦ (q - 1) * (q ^ j - q ^ (-j - 1))
  have hW (j : ℤ) (hj : j ∈ I) : 0 ≤ W j := by
    have hjr := Finset.mem_Icc.mp hj
    dsimp [W]
    exact mul_nonneg (by linarith)
      (sub_nonneg.mpr (zpow_le_zpow_right₀ hq.le (by omega)))
  have hcolumns :
      (∑ j ∈ I, (q ^ t * (q ^ j + q ^ (-j)) - 2) * W j) ≤
        ∑ j ∈ I, ((gridA q t j).card : ℝ) * W j := by
    apply Finset.sum_le_sum
    intro j hj
    have hjr := Finset.mem_Icc.mp hj
    exact mul_le_mul_of_nonneg_right
      (grid_case4_column_card_lower q hq L hq2L t j ht hjr.1 hjr.2) (hW j hj)
  have hIcardZ : (I.card : ℤ) = (L : ℤ) := by
    dsimp [I]
    rw [Int.card_Icc_of_le 0 ((L : ℤ) - 1) (by omega)]
    omega
  have hIcard : (I.card : ℝ) = L := by exact_mod_cast hIcardZ
  have hsquare := grid_case4_square_sum q hq L hL hq2L
  have hweight := sum_Icc_zpow_difference q hqne 0 ((L : ℤ) - 1) (by omega)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsInv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp [hspos.ne']
    nlinarith [hsSq]
  have hnL : q ^ (-(L : ℤ)) = Real.sqrt 2 / 2 := by
    rw [zpow_neg, hqL]
    simpa [one_div] using hsInv
  have hweight' : ∑ j ∈ I, W j = 3 * Real.sqrt 2 / 2 - 2 := by
    dsimp [I, W]
    rw [hweight]
    rw [show (L : ℤ) - 1 + 1 = (L : ℤ) by omega,
      show -((L : ℤ) - 1) - 1 = -(L : ℤ) by omega, hqL, hnL]
    norm_num
    ring
  have hsquare' :
      ∑ j ∈ I, (q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1)) =
        (1 - q / 2) / (1 + q) := by
    simpa [I] using hsquare
  have hexpand :
      (∑ j ∈ I, (q ^ t * (q ^ j + q ^ (-j)) - 2) * W j) =
        q ^ t / (1 + q) * (1 - q / 2) +
          (L : ℝ) * ((q - 1) * q ^ t * (1 - 1 / q)) +
          4 - 3 * Real.sqrt 2 := by
    have hsumA :
        (∑ j ∈ I, q ^ t *
          ((q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1)))) =
        q ^ t * (∑ j ∈ I,
          (q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1))) := by
      rw [Finset.mul_sum]
    have hsumC : (∑ j ∈ I, 2 * W j) = 2 * (∑ j ∈ I, W j) := by
      rw [Finset.mul_sum]
    calc
      _ = ∑ j ∈ I,
          (q ^ t * ((q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1))) +
            (q - 1) * q ^ t * (1 - 1 / q) - 2 * W j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact grid_case4_summand_expand q hq t j
      _ = q ^ t * (∑ j ∈ I,
            (q - 1) * (q ^ (2 * j) - q ^ (-2 * j - 1))) +
          (I.card : ℝ) * ((q - 1) * q ^ t * (1 - 1 / q)) -
          2 * (∑ j ∈ I, W j) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          hsumA, Finset.sum_const, nsmul_eq_mul, hsumC]
      _ = _ := by
        rw [hsquare', hIcard, hweight']
        ring
  have hmiddle :
      0 ≤ (L : ℝ) * ((q - 1) * q ^ t * (1 - 1 / q)) := by
    have hqinv : 1 / q ≤ 1 := (div_le_one hqpos).2 hq.le
    positivity
  have hlower :
      q ^ t / (2 * (1 + q)) * (1 - q / 2) + 2 - 3 * Real.sqrt 2 / 2 ≤
        (1 / 2 : ℝ) *
          ∑ j ∈ I, (q ^ t * (q ^ j + q ^ (-j)) - 2) * W j := by
    have hqadd : 1 + q ≠ 0 := by linarith
    have hid :
        q ^ t / (2 * (1 + q)) * (1 - q / 2) + 2 - 3 * Real.sqrt 2 / 2 =
          (1 / 2 : ℝ) *
            (q ^ t / (1 + q) * (1 - q / 2) + 4 - 3 * Real.sqrt 2) := by
      field_simp [hqadd]
      ring
    rw [hid, hexpand]
    exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  have hhalf := mul_le_mul_of_nonneg_left hcolumns (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact hlower.trans (by simpa [I, W, mul_assoc] using hhalf)

end Erdos441
