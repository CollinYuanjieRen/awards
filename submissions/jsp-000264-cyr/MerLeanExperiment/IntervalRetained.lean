import MerLeanExperiment.FiniteTail
import MerLeanExperiment.SmallOmittedMass

namespace ReciprocalSquares

/-- A second, coarser tail bound makes the omitted mass a relative error. -/
theorem finite_square_interval_lower (d : ℕ) (hd : 2 ≤ d) :
    (9 : ℚ) / (10 * ((d : ℚ) + 1)) ≤
      ∑ j ∈ Finset.Icc (d + 1) (20 * d), (1 : ℚ) / (j : ℚ) ^ 2 := by
  have htel : ∀ b : ℕ, d + 1 ≤ b →
      (∑ j ∈ Finset.Icc (d + 1) b,
        (1 : ℚ) / ((j : ℚ) * ((j : ℚ) + 1))) =
        1 / ((d : ℚ) + 1) - 1 / ((b : ℚ) + 1) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton]
      push_cast
      field_simp
      ring
    | succ b hb ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hb), ih]
      push_cast
      field_simp
      ring
  have hdQ : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have hscalar : (9 : ℚ) / (10 * ((d : ℚ) + 1)) ≤
      1 / ((d : ℚ) + 1) - 1 / (20 * (d : ℚ) + 1) := by
    apply (le_sub_iff_add_le).mpr
    have hd1 : 0 < (d : ℚ) + 1 := by positivity
    have hd20 : 0 < 20 * (d : ℚ) + 1 := by positivity
    field_simp
    nlinarith
  calc
    (9 : ℚ) / (10 * ((d : ℚ) + 1)) ≤
        1 / ((d : ℚ) + 1) - 1 / (20 * (d : ℚ) + 1) := hscalar
    _ = ∑ j ∈ Finset.Icc (d + 1) (20 * d),
        (1 : ℚ) / ((j : ℚ) * ((j : ℚ) + 1)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using (htel (20 * d) (by omega)).symm
    _ ≤ ∑ j ∈ Finset.Icc (d + 1) (20 * d), (1 : ℚ) / (j : ℚ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjpos : 0 < (j : ℚ) := by
        exact_mod_cast (show 0 < j by have := (Finset.mem_Icc.mp hj).1; omega)
      apply one_div_le_one_div_of_le (pow_pos hjpos 2)
      nlinarith

/-- Losing the omitted roots preserves a fixed fraction of each prefix tail. -/
theorem retained_interval_mass_lower (N d : ℕ) (ε : ℚ)
    (hN : 20 < N) (hd : 2 ≤ d) (hdN : d < N ^ 2)
    (hεN : 3 ≤ ε ^ 2 * (N : ℚ)) :
    (1 - ε ^ 2) * (∑ j ∈ Finset.Icc (d + 1) (20 * d),
      (1 : ℚ) / (j : ℚ) ^ 2) ≤
    ∑ j ∈ (Finset.Icc (d + 1) (20 * d)) ∩ rootsZ N,
      (1 : ℚ) / (j : ℚ) ^ 2 := by
  let I := Finset.Icc (d + 1) (20 * d)
  let T : ℚ := ∑ j ∈ I, (1 : ℚ) / (j : ℚ) ^ 2
  have hNQ : (0 : ℚ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound : 20 * d < N ^ 3 := by
    calc
      20 * d < 20 * N ^ 2 := Nat.mul_lt_mul_of_pos_left hdN (by omega)
      _ ≤ N * N ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = N ^ 3 := by ring
  have hmissing := small_omitted_square_mass_finset_le N (by omega) (I \ rootsZ N)
    (by
      intro n hn
      obtain ⟨hnI, hnmiss⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hnI
      exact ⟨by omega, hnhi.trans_lt hbound, hnmiss⟩)
  have hdQ : (d : ℚ) + 1 ≤ (N : ℚ) ^ 2 := by exact_mod_cast hdN
  have hT : (9 : ℚ) / (10 * (N : ℚ) ^ 2) ≤ T := by
    apply le_trans _ (finite_square_interval_lower d hd)
    apply div_le_div_of_nonneg_left (by norm_num)
      (by positivity : (0 : ℚ) < 10 * ((d : ℚ) + 1))
    linarith
  have hrelative : (2 : ℚ) / (N : ℚ) ^ 3 ≤
      ε ^ 2 * (9 / (10 * (N : ℚ) ^ 2)) := by
    apply (div_le_iff₀ (pow_pos hNQ 3)).mpr
    have hid : ε ^ 2 * (9 / (10 * (N : ℚ) ^ 2)) * (N : ℚ) ^ 3 =
        9 / 10 * (ε ^ 2 * (N : ℚ)) := by field_simp
    rw [hid]
    linarith
  have herror : (2 : ℚ) / (N : ℚ) ^ 3 ≤ ε ^ 2 * T :=
    hrelative.trans (mul_le_mul_of_nonneg_left hT (sq_nonneg ε))
  have hsplit := Finset.sum_inter_add_sum_sdiff I (rootsZ N)
    (fun j => (1 : ℚ) / (j : ℚ) ^ 2)
  change (1 - ε ^ 2) * T ≤ _
  change _ + _ = T at hsplit
  nlinarith

/-- The concrete retained interval supplies the strict greedy slack. -/
theorem retained_interval_greedy_slack (N d : ℕ) (ε : ℚ)
    (hN : 20 < N) (hd : 2 ≤ d) (hdN : d < N ^ 2)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10)
    (hεN : 3 ≤ ε ^ 2 * (N : ℚ)) :
    (1 + ε / 8) * ((1 : ℚ) / (d : ℚ) ^ 2) <
      (1 - ε) * ∑ j ∈ (Finset.Icc (d + 1) (20 * d)) ∩ rootsZ N,
        (1 : ℚ) / (j : ℚ) ^ 2 := by
  have hεsq : ε ^ 2 ≤ 1 / 100 := by nlinarith
  have hprod : (891 : ℚ) / 1000 ≤ (1 - ε) * (1 - ε ^ 2) := by
    have := mul_le_mul (show (9 : ℚ) / 10 ≤ 1 - ε by linarith)
      (show (99 : ℚ) / 100 ≤ 1 - ε ^ 2 by linarith)
      (by norm_num : (0 : ℚ) ≤ 99 / 100) (by linarith : 0 ≤ 1 - ε)
    norm_num at this
    exact this
  have hscalar : 1 + ε / 8 < (1 - ε) * (1 - ε ^ 2) * (121 / 100) := by
    nlinarith
  have hdQ : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hpositive : 0 < (1 - ε) * (1 - ε ^ 2) := by nlinarith
  have htail := mul_lt_mul_of_pos_left (finite_reciprocal_square_tail d hd) hpositive
  have hkeep := mul_le_mul_of_nonneg_left
    (retained_interval_mass_lower N d ε hN hd hdN hεN)
    (by linarith : 0 ≤ 1 - ε)
  have hfirst := mul_lt_mul_of_pos_right hscalar
    (by positivity : (0 : ℚ) < 1 / (d : ℚ) ^ 2)
  calc
    (1 + ε / 8) * ((1 : ℚ) / (d : ℚ) ^ 2) <
        (1 - ε) * (1 - ε ^ 2) * (121 / (100 * (d : ℚ) ^ 2)) := by
      have heq : (1 - ε) * (1 - ε ^ 2) * (121 / (100 * (d : ℚ) ^ 2)) =
          (1 - ε) * (1 - ε ^ 2) * (121 / 100) * (1 / (d : ℚ) ^ 2) := by
        ring
      rw [heq]
      exact hfirst
    _ < (1 - ε) * (1 - ε ^ 2) *
        (∑ j ∈ Finset.Icc (d + 1) (20 * d), (1 : ℚ) / (j : ℚ) ^ 2) := htail
    _ ≤ (1 - ε) * ∑ j ∈ (Finset.Icc (d + 1) (20 * d)) ∩ rootsZ N,
        (1 : ℚ) / (j : ℚ) ^ 2 := by
      simpa only [mul_assoc] using hkeep

end ReciprocalSquares
