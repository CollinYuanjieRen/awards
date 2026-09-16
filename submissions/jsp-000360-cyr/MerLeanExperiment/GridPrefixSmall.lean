import MerLeanExperiment.GridPrefixIdentity

namespace Erdos441

open scoped BigOperators

private lemma grid_weight_nonneg (q : ℝ) (hq : 1 < q) (j : ℤ) :
    0 ≤ q ^ j * (q - 1) := mul_nonneg (zpow_nonneg (by linarith) _) (by linarith)

theorem grid_prefix_case_neg (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (T t : ℤ) (hT : 0 ≤ T) (htlo : -T ≤ t) (htneg : t < 0) :
    gridBetaPrefix q L T t ≤ gridCapacityPrefix q L T t := by
  rw [grid_capacity_prefix_eq q hq L hL T t hT htlo]
  have hbeta : gridBetaPrefix q L T t =
      ∑ i ∈ Finset.Icc (-T) t, q ^ i * (q - 1) := by
    unfold gridBetaPrefix
    apply Finset.sum_congr rfl
    intro i hi
    have hit : i ≤ t := (Finset.mem_Icc.mp hi).2
    simp [gridBeta, show i < (L : ℤ) by omega]
  rw [hbeta]
  have hsubset : Finset.Icc (-T) t ⊆ Finset.Icc (-T) (-1) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have hcard :
      (∑ j ∈ Finset.Icc (-T) t, q ^ j * (q - 1)) ≤
        ∑ j ∈ Finset.Icc (-T) t,
          (gridA q t j).card * q ^ j * (q - 1) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjt : j ≤ t := (Finset.mem_Icc.mp hj).2
    have hmem := zero_mem_grid_column q hq t j hjt
    have hc : (1 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast Finset.one_le_card.mpr ⟨0, hmem⟩
    have hw := grid_weight_nonneg q hq j
    calc
      q ^ j * (q - 1) ≤ ((gridA q t j).card : ℝ) * (q ^ j * (q - 1)) :=
        by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hw
      _ = _ := by ring_nf
  have hcardFull :
      (∑ j ∈ Finset.Icc (-T) t,
          (gridA q t j).card * q ^ j * (q - 1)) ≤
        ∑ j ∈ Finset.Icc (-T) (-1),
          (gridA q t j).card * q ^ j * (q - 1) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j _ _ => by positivity)
  have hposzero :
      (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : 0 ≤ j := (Finset.mem_Icc.mp hj).1
    simp [gridA, show ¬ j ≤ t by omega]
  rw [hposzero]
  simp only [mul_zero, add_zero]
  simp [show ¬ 0 ≤ t by omega]
  exact hcard.trans hcardFull

theorem grid_prefix_case_small (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (T t : ℤ) (hT : 0 ≤ T) (hcover : (L : ℤ) - 1 ≤ T)
    (ht0 : 0 ≤ t) (htL : t < (L : ℤ)) :
    gridBetaPrefix q L T t ≤ gridCapacityPrefix q L T t := by
  have htT : t ≤ T := by omega
  rw [grid_capacity_prefix_eq q hq L hL T t hT (by omega)]
  have hbeta : gridBetaPrefix q L T t = q ^ (t + 1) - q ^ (-T) := by
    unfold gridBetaPrefix
    calc
      _ = ∑ i ∈ Finset.Icc (-T) t, q ^ i * (q - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiL : i < (L : ℤ) := (Finset.mem_Icc.mp hi).2.trans_lt htL
        simp [gridBeta, hiL]
      _ = _ := sum_Icc_zpow_mul_sub_one q (by linarith) (-T) t (by omega)
  rw [hbeta]
  simp [ht0]
  let wn : ℤ → ℝ := fun j => q ^ j * (q - 1)
  have hneg :
      (∑ j ∈ Finset.Icc (-T) (-1), wn j) +
          (∑ j ∈ Finset.Icc (-t) (-1), wn j) ≤
        ∑ j ∈ Finset.Icc (-T) (-1),
          (gridA q t j).card * q ^ j * (q - 1) := by
    have hsub : Finset.Icc (-t) (-1) ⊆ Finset.Icc (-T) (-1) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    have heq :
        (∑ j ∈ Finset.Icc (-T) (-1), wn j) + (∑ j ∈ Finset.Icc (-t) (-1), wn j) =
          ∑ j ∈ Finset.Icc (-T) (-1), (wn j + if -t ≤ j then wn j else 0) := by
      rw [Finset.sum_add_distrib]
      congr 1
      have hfilter : (Finset.Icc (-T) (-1)).filter (fun j => -t ≤ j) = Finset.Icc (-t) (-1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [← hfilter, Finset.sum_filter]
    rw [heq]
    apply Finset.sum_le_sum
    intro j hj
    have hjr := Finset.mem_Icc.mp hj
    have hjt : j ≤ t := by omega
    have hw := grid_weight_nonneg q hq j
    by_cases hextra : -t ≤ j
    · have hs : 0 ≤ t + j := by omega
      have htwoN : 2 ≤ (gridA q t j).card :=
        Finset.card_le_card (zero_one_subset_grid_column q hq t j hjt hs)
      have htwo : (2 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast htwoN
      simp [hextra, wn]
      nlinarith
    · have honeN : 1 ≤ (gridA q t j).card :=
        Finset.one_le_card.mpr ⟨0, zero_mem_grid_column q hq t j hjt⟩
      have hone : (1 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast honeN
      simp [hextra, wn]
      nlinarith
  have hpos :
      (∑ j ∈ Finset.Icc 0 t, (q - 1) * (q ^ j - q ^ (-j - 1))) ≤
        (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)) := by
    rw [Finset.mul_sum]
    have hsub : Finset.Icc 0 t ⊆ Finset.Icc 0 ((L : ℤ) - 1) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    have hrestrict :
        (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (1 / 2 : ℝ) * ((gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)))) =
        ∑ j ∈ Finset.Icc 0 t,
          (1 / 2 : ℝ) * ((gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1))) := by
      symm
      apply Finset.sum_subset hsub
      intro j hjbig hjnot
      have hj := Finset.mem_Icc.mp hjbig
      have hjt : ¬ j ≤ t := by
        intro h
        exact hjnot (by simp [hj.1, h])
      simp [gridA, hjt]
    rw [hrestrict]
    apply Finset.sum_le_sum
    intro j hj
    have hjr := Finset.mem_Icc.mp hj
    have htwoN : 2 ≤ (gridA q t j).card := by
      have hs := zero_one_subset_grid_column q hq t j hjr.2 (by omega)
      have := Finset.card_le_card hs
      simpa using this
    have htwo : (2 : ℝ) ≤ (gridA q t j).card := by exact_mod_cast htwoN
    have hzpow : q ^ (-j - 1) ≤ q ^ j :=
      zpow_le_zpow_right₀ (le_of_lt hq) (by omega)
    have hw : 0 ≤ (q - 1) * (q ^ j - q ^ (-j - 1)) := mul_nonneg (by linarith) (sub_nonneg.mpr hzpow)
    nlinarith
  have hs1 := sum_Icc_zpow_mul_sub_one q (by linarith) (-T) (-1) (by omega)
  have hs2 := sum_Icc_zpow_mul_sub_one q (by linarith) (-t) (-1) (by omega)
  have hs3 :
      (∑ j ∈ Finset.Icc 0 t, (q - 1) * (q ^ j - q ^ (-j - 1))) =
        q ^ (t + 1) - 2 + q ^ (-t - 1) := by
    have hf := sum_Icc_zpow_mul_sub_one q (by linarith) 0 t (by omega)
    have hb := sum_Icc_backward_sub (fun j => q ^ (-j - 1)) 0 t (by omega)
    calc
      _ = (∑ j ∈ Finset.Icc 0 t, q ^ j * (q - 1)) -
          ∑ j ∈ Finset.Icc 0 t, (q ^ (-j) - q ^ (-j - 1)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [zpow_sub_one₀ (by linarith : q ≠ 0)]
            field_simp
      _ = _ := by
        rw [hf]
        have hb' : (∑ j ∈ Finset.Icc 0 t, (q ^ (-j) - q ^ (-j - 1))) =
            1 - q ^ (-t - 1) := by
          rw [← neg_inj]
          rw [← Finset.sum_neg_distrib]
          convert hb using 1
          · apply Finset.sum_congr rfl
            intro j _
            ring_nf
          · norm_num
        rw [hb']
        norm_num
        ring_nf
  have hlower := add_le_add (add_le_add hneg hpos) (le_refl (1 - q ^ (-1 : ℤ)))
  rw [hs1, hs2, hs3] at hlower
  norm_num only [Int.reduceNeg, add_neg_cancel, zpow_zero] at hlower
  have hrem : 0 ≤ (1 - q ^ (-1 : ℤ)) * (1 - q ^ (-t : ℤ)) := by
    have hqinv : q ^ (-1 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (le_of_lt hq) (by omega)
    have hqt : q ^ (-t : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (le_of_lt hq) (by omega)
    exact mul_nonneg (sub_nonneg.mpr hqinv) (sub_nonneg.mpr hqt)
  have hid :
      (1 - q ^ (-T)) + (1 - q ^ (-t)) +
          (q ^ (t + 1) - 2 + q ^ (-t - 1)) + (1 - q ^ (-1 : ℤ)) =
        (q ^ (t + 1) - q ^ (-T)) +
          (1 - q ^ (-1 : ℤ)) * (1 - q ^ (-t)) := by
    have hz : q ^ (-t - 1) = q ^ (-t) * q ^ (-1 : ℤ) := by
      rw [← zpow_add₀ (by linarith : q ≠ 0)]
      congr 1
    rw [hz]
    ring_nf
  rw [hid] at hlower
  have hlower' :
      (q ^ (t + 1) + (1 - q ^ (-1 : ℤ)) * (1 - q ^ (-t))) - q ^ (-T) ≤
        (∑ j ∈ Finset.Icc (-T) (-1), (gridA q t j).card * q ^ j * (q - 1)) +
        (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
          (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1))) +
        (1 - q ^ (-1 : ℤ)) := by
    linarith
  have hshift := (sub_le_iff_le_add).mp hlower'
  exact (le_add_of_nonneg_right hrem).trans (by simpa [zpow_neg] using hshift)

end Erdos441

