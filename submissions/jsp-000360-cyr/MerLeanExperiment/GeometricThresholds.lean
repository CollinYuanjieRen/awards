import MerLeanExperiment.IntTelescoping
import Mathlib.Tactic

namespace Erdos441

theorem geom_tail_lower (q : ℝ) (hq : 1 < q) (T : ℤ) (hT : 0 ≤ T) (s : ℝ)
    (hs : q ^ (-T) ≤ s) :
    1 - q * s ≤ ∑ j ∈ (Finset.Icc (-T) (-1)).filter (fun j => s ≤ q ^ j),
      q ^ j * (q - 1) := by
  let A := (Finset.Icc (-T) (-1)).filter (fun j => s ≤ q ^ j)
  have hq0 : 0 < q := zero_lt_one.trans hq
  by_cases hA : A.Nonempty
  · let j0 := A.min' hA
    have hj0A : j0 ∈ A := Finset.min'_mem A hA
    have hj0 : j0 ∈ Finset.Icc (-T) (-1) := (Finset.mem_filter.1 hj0A).1
    have hsj0 : s ≤ q ^ j0 := (Finset.mem_filter.1 hj0A).2
    have hset : A = Finset.Icc j0 (-1) := by
      ext j
      constructor
      · intro hjA
        have hj := Finset.mem_filter.1 hjA
        exact Finset.mem_Icc.2 ⟨Finset.min'_le A j hjA, (Finset.mem_Icc.1 hj.1).2⟩
      · intro hjI
        have hjbounds := Finset.mem_Icc.1 hjI
        have hj0bounds := Finset.mem_Icc.1 hj0
        refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hj0bounds.1.trans hjbounds.1,
          hjbounds.2⟩, hsj0.trans ?_⟩
        exact zpow_le_zpow_right₀ hq.le hjbounds.1
    have hj0bound : q ^ j0 ≤ q * s := by
      by_cases heq : j0 = -T
      · rw [heq]
        have hs0 : 0 ≤ s := (zpow_pos hq0 _).le.trans hs
        nlinarith
      · have hj0bounds := Finset.mem_Icc.1 hj0
        have hjgt : -T < j0 := lt_of_le_of_ne hj0bounds.1 (Ne.symm heq)
        have hjpred : j0 - 1 ∈ Finset.Icc (-T) (-1) := by
          simp only [Finset.mem_Icc]
          omega
        have hfail : ¬s ≤ q ^ (j0 - 1) := by
          intro hp
          have hm : j0 - 1 ∈ A := Finset.mem_filter.2 ⟨hjpred, hp⟩
          have := Finset.min'_le A (j0 - 1) hm
          omega
        have hp_lt : q ^ (j0 - 1) < s := lt_of_not_ge hfail
        rw [show j0 = (j0 - 1) + 1 by ring, zpow_add_one₀ hq0.ne']
        simpa [mul_comm] using (mul_lt_mul_of_pos_right hp_lt hq0).le
    change 1 - q * s ≤ ∑ j ∈ A, q ^ j * (q - 1)
    rw [hset, sum_Icc_zpow_mul_sub_one q hq0.ne' j0 (-1) (by
      have hj0bounds := Finset.mem_Icc.1 hj0
      omega)]
    norm_num
    linarith
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change 1 - q * s ≤ ∑ j ∈ A, q ^ j * (q - 1)
    rw [hAempty]
    simp only [Finset.sum_empty]
    by_cases hT0 : T = 0
    · subst T
      norm_num at hs
      nlinarith
    · have hm1base : (-1 : ℤ) ∈ Finset.Icc (-T) (-1) := by
        simp only [Finset.mem_Icc]
        omega
      have hnot : ¬s ≤ q ^ (-1 : ℤ) := by
        intro hp
        have : (-1 : ℤ) ∈ A := Finset.mem_filter.2 ⟨hm1base, hp⟩
        rw [hAempty] at this
        simp at this
      have hinv : q ^ (-1 : ℤ) = q⁻¹ := by simp
      rw [hinv] at hnot
      have hmul : 1 < q * s := by
        have := lt_of_not_ge hnot
        calc
          1 = q * q⁻¹ := by field_simp
          _ < q * s := mul_lt_mul_of_pos_left this hq0
      linarith

theorem geom_tail_upper (q : ℝ) (hq : 1 < q) (T : ℤ) (_hT : 0 ≤ T) (h : ℝ)
    (_hh0 : 0 < h) (hh1 : h < 1) :
    (∑ j ∈ (Finset.Icc (-T) (-1)).filter (fun j => h < q ^ j),
      q ^ j * (q - 1)) ≤ 1 - h := by
  let A := (Finset.Icc (-T) (-1)).filter (fun j => h < q ^ j)
  have hq0 : 0 < q := zero_lt_one.trans hq
  by_cases hA : A.Nonempty
  · let j0 := A.min' hA
    have hj0A : j0 ∈ A := Finset.min'_mem A hA
    have hj0 : j0 ∈ Finset.Icc (-T) (-1) := (Finset.mem_filter.1 hj0A).1
    have hhj0 : h < q ^ j0 := (Finset.mem_filter.1 hj0A).2
    have hset : A = Finset.Icc j0 (-1) := by
      ext j
      constructor
      · intro hjA
        have hj := Finset.mem_filter.1 hjA
        exact Finset.mem_Icc.2 ⟨Finset.min'_le A j hjA, (Finset.mem_Icc.1 hj.1).2⟩
      · intro hjI
        have hjbounds := Finset.mem_Icc.1 hjI
        have hj0bounds := Finset.mem_Icc.1 hj0
        refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hj0bounds.1.trans hjbounds.1,
          hjbounds.2⟩, hhj0.trans_le ?_⟩
        exact zpow_le_zpow_right₀ hq.le hjbounds.1
    change (∑ j ∈ A, q ^ j * (q - 1)) ≤ 1 - h
    rw [hset, sum_Icc_zpow_mul_sub_one q hq0.ne' j0 (-1) (by
      have hj0bounds := Finset.mem_Icc.1 hj0
      omega)]
    norm_num
    linarith
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change (∑ j ∈ A, q ^ j * (q - 1)) ≤ 1 - h
    rw [hAempty]
    simp only [Finset.sum_empty]
    linarith

theorem geom_band_lower (q : ℝ) (hq : 1 < q) (T : ℤ) (hT : 0 ≤ T)
    (s h : ℝ) (hs : q ^ (-T) ≤ s) (hh0 : 0 < h) (hh1 : h < 1) :
    h - q * s ≤ ∑ j ∈ (Finset.Icc (-T) (-1)).filter
      (fun j => s ≤ q ^ j ∧ q ^ j ≤ h), q ^ j * (q - 1) := by
  have hw (j : ℤ) : 0 ≤ q ^ j * (q - 1) :=
    mul_nonneg (zpow_nonneg (by linarith) _) (by linarith)
  by_cases hsh : s ≤ h
  · let J := Finset.Icc (-T) (-1)
    let L := J.filter (fun j => s ≤ q ^ j)
    let U := J.filter (fun j => h < q ^ j)
    let B := J.filter (fun j => s ≤ q ^ j ∧ q ^ j ≤ h)
    have hpart : L = B ∪ U := by
      ext j
      simp only [L, B, U, J, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
      constructor
      · rintro ⟨hj, hsj⟩
        by_cases hjh : q ^ j ≤ h
        · exact Or.inl ⟨hj, hsj, hjh⟩
        · exact Or.inr ⟨hj, lt_of_not_ge hjh⟩
      · rintro (hj | hj)
        · exact ⟨hj.1, hj.2.1⟩
        · exact ⟨hj.1, hsh.trans hj.2.le⟩
    have hdisj : Disjoint B U := by
      refine Finset.disjoint_left.2 ?_
      intro j hjB hjU
      have hb := (Finset.mem_filter.1 hjB).2.2
      have hu := (Finset.mem_filter.1 hjU).2
      linarith
    have hsum : (∑ j ∈ L, q ^ j * (q - 1)) =
        (∑ j ∈ B, q ^ j * (q - 1)) + (∑ j ∈ U, q ^ j * (q - 1)) := by
      rw [hpart, Finset.sum_union hdisj]
    have hl := geom_tail_lower q hq T hT s hs
    have hu := geom_tail_upper q hq T hT h hh0 hh1
    change 1 - q * s ≤ ∑ j ∈ L, q ^ j * (q - 1) at hl
    change (∑ j ∈ U, q ^ j * (q - 1)) ≤ 1 - h at hu
    change h - q * s ≤ ∑ j ∈ B, q ^ j * (q - 1)
    linarith
  · have hneg : h - q * s ≤ 0 := by
      have hspos : 0 < s := hh0.trans (lt_of_not_ge hsh)
      nlinarith
    exact hneg.trans (Finset.sum_nonneg fun j _ => hw j)

end Erdos441
