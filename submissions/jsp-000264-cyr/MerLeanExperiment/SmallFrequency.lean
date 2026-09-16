import MerLeanExperiment.SquareSupport
import MerLeanExperiment.SquareMass
import MerLeanExperiment.FourierBridge

namespace ReciprocalSquares

/-- The absolute cubic angle sum factors through the cubic reciprocal moment. -/
theorem sum_cubic_angles_eq (D : Finset ℕ) (h : ℤ) :
    (∑ d ∈ D, |2 * Real.pi * (h : ℝ) / (d : ℝ)| ^ 3 / 3) =
      (2 * Real.pi * |(h : ℝ)|) ^ 3 / 3 *
        ∑ d ∈ D, (1 : ℝ) / (d : ℝ) ^ 3 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  simp only [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos,
    abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  ring

/-- On the concrete small-frequency range, every centered factor has a small angle. -/
theorem small_frequency_angle_le_one (M : ℕ) (hM : 32 ≤ M) (h : ℤ)
    (hh : |(h : ℝ)| ≤ (M : ℝ) ^ 16) :
    ∀ d ∈ squareD (M ^ 10), |2 * Real.pi * (h : ℝ) / (d : ℝ)| ≤ 1 := by
  have hMR : (32 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hM10 : 2 ≤ M ^ 10 := by
    calc
      2 ≤ 32 ^ 10 := by norm_num
      _ ≤ M ^ 10 := Nat.pow_le_pow_left hM 10
  have hM4 : (8 : ℝ) ≤ (M : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hMR 4
    norm_num at this
    linarith
  have hcoeff : 2 * Real.pi ≤ (M : ℝ) ^ 4 := by
    linarith [Real.pi_lt_four]
  intro d hd
  have hdscale : (M : ℝ) ^ 20 < d := by
    have := squareD_gt_scale (M ^ 10) hM10 d hd
    exact_mod_cast (by simpa only [← pow_mul] using this)
  have hdpos : (0 : ℝ) < d := lt_trans (pow_pos hM0 20) hdscale
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos,
    abs_of_pos hdpos]
  apply (div_le_one hdpos).mpr
  calc
    2 * Real.pi * |(h : ℝ)| ≤ 2 * Real.pi * (M : ℝ) ^ 16 :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ (M : ℝ) ^ 4 * (M : ℝ) ^ 16 :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = (M : ℝ) ^ 20 := by ring
    _ ≤ d := hdscale.le

/-- The full cubic angle error is below the product-positivity threshold. -/
theorem small_frequency_cubic_sum_lt_log_two (M : ℕ) (hM : 32 ≤ M) (h : ℤ)
    (hh : |(h : ℝ)| ≤ (M : ℝ) ^ 16) :
    (∑ d ∈ squareD (M ^ 10),
      |2 * Real.pi * (h : ℝ) / (d : ℝ)| ^ 3 / 3) < Real.log 2 := by
  have hMR : (32 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hM10 : 2 ≤ M ^ 10 := by
    calc
      2 ≤ 32 ^ 10 := by norm_num
      _ ≤ M ^ 10 := Nat.pow_le_pow_left hM 10
  have hmass : (∑ d ∈ squareD (M ^ 10), (1 : ℝ) / (d : ℝ) ^ 3) ≤
      3 / (M : ℝ) ^ 50 := by
    simpa only [Nat.cast_pow, ← pow_mul] using squareD_recip_cube_sum_le (M ^ 10) hM10
  have hcoef : (2 * Real.pi * |(h : ℝ)|) ^ 3 / 3 ≤
      (2 * Real.pi * (M : ℝ) ^ 16) ^ 3 / 3 := by
    gcongr
  have hpi3 : Real.pi ^ 3 < (4 : ℝ) ^ 3 := by
    gcongr
    exact Real.pi_lt_four
  have hMsq : (1024 : ℝ) ≤ (M : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hMR 2
    norm_num at this
    exact this
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at this ⊢
    linarith
  calc
    (∑ d ∈ squareD (M ^ 10),
        |2 * Real.pi * (h : ℝ) / (d : ℝ)| ^ 3 / 3) =
        (2 * Real.pi * |(h : ℝ)|) ^ 3 / 3 *
          ∑ d ∈ squareD (M ^ 10), (1 : ℝ) / (d : ℝ) ^ 3 :=
      sum_cubic_angles_eq _ h
    _ ≤ (2 * Real.pi * (M : ℝ) ^ 16) ^ 3 / 3 * (3 / (M : ℝ) ^ 50) :=
      mul_le_mul hcoef hmass (by positivity) (by positivity)
    _ = 8 * Real.pi ^ 3 / (M : ℝ) ^ 2 := by
      field_simp [ne_of_gt hM0]
      ring
    _ < 512 / (M : ℝ) ^ 2 := by
      apply (div_lt_div_iff_of_pos_right (pow_pos hM0 2)).mpr
      nlinarith
    _ ≤ 1 / 2 := by
      apply (div_le_iff₀ (pow_pos hM0 2)).mpr
      linarith
    _ ≤ Real.log 2 := hlog

/-- The concrete low-frequency part of the square-denominator product is positive. -/
theorem small_frequency_centeredProduct_re_pos (M : ℕ) (hM : 32 ≤ M)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℤ)
    (hh : |(h : ℝ)| ≤ (M : ℝ) ^ 16) :
    0 < (centeredProduct (squareD (M ^ 10)) p h).re := by
  exact prod_centeredFactor_re_pos (squareD (M ^ 10)) (fun _ => p)
    (fun d => 2 * Real.pi * (h : ℝ) / (d : ℝ))
    (fun _ _ => hp0) (fun _ _ => hp1)
    (small_frequency_angle_le_one M hM h hh)
    (small_frequency_cubic_sum_lt_log_two M hM h hh)

end ReciprocalSquares
