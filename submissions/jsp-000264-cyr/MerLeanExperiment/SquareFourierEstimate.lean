import MerLeanExperiment.SmallFrequency
import MerLeanExperiment.BottomFrequency
import MerLeanExperiment.MiddleFrequency
import MerLeanExperiment.FiniteFrequencyBounds
import MerLeanExperiment.HighFrequencyEnergy
import MerLeanExperiment.AtomBound

namespace ReciprocalSquares

instance squareModulus_neZero (N : ℕ) : NeZero (squareModulus N) :=
  ⟨(squareModulus_pos N).ne'⟩

/-- The high-frequency decay absorbs the entire Fourier modulus. -/
theorem squareModulus_mul_high_decay_le (M : ℕ) (hM : 262144 ≤ M) (κ : ℝ)
    (hscale : 121 ≤ 8 * κ * highFrequencyConstant * (M : ℝ) ^ 20) :
    (squareModulus (M ^ 10) : ℝ) *
      Real.exp (-8 * κ * highFrequencyConstant * (M : ℝ) ^ 51) ≤
        Real.exp (-(M : ℝ)) := by
  have hmpos : (0 : ℝ) < squareModulus (M ^ 10) := by
    exact_mod_cast squareModulus_pos (M ^ 10)
  have hpower : (M : ℝ) ≤ (M : ℝ) ^ 31 :=
    le_self_pow₀ (by exact_mod_cast (show 1 ≤ M by omega)) (by decide)
  have hlog := squareModulus_log_le_power M hM
  have hmul := mul_le_mul_of_nonneg_right hscale
    (show (0 : ℝ) ≤ (M : ℝ) ^ 31 by positivity)
  have hdecay : 121 * (M : ℝ) ^ 31 ≤
      8 * κ * highFrequencyConstant * (M : ℝ) ^ 51 := by
    calc
      121 * (M : ℝ) ^ 31 ≤
          (8 * κ * highFrequencyConstant * (M : ℝ) ^ 20) * (M : ℝ) ^ 31 := hmul
      _ = 8 * κ * highFrequencyConstant * (M : ℝ) ^ 51 := by ring
  calc
    (squareModulus (M ^ 10) : ℝ) *
        Real.exp (-8 * κ * highFrequencyConstant * (M : ℝ) ^ 51) =
      Real.exp (Real.log (squareModulus (M ^ 10) : ℝ) -
        8 * κ * highFrequencyConstant * (M : ℝ) ^ 51) := by
          rw [Real.exp_sub, Real.exp_log hmpos, div_eq_mul_inv, ← Real.exp_neg]
          congr 2
          ring
    _ ≤ Real.exp (-(M : ℝ)) := Real.exp_le_exp.mpr (by linarith)

set_option exponentiation.threshold 1024 in
/-- All nonsmall centered frequencies together have norm less than one half. -/
theorem square_sum_norm_outside_small_lt_half
    (M : ℕ) (hM : 262144 ≤ M) (p κ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hκ0 : 0 < κ) (hκ : κ ≤ p * (1 - p))
    (hscale : 121 ≤ 8 * κ * highFrequencyConstant * (M : ℝ) ^ 20)
    (htail : (4 * (M : ℝ) ^ 360 + 2) * Real.exp (-κ * (M : ℝ) / 128) +
      Real.exp (-(M : ℝ)) < 1 / 2) :
    (∑ h ∈ Finset.univ.filter (fun h : ZMod (squareModulus (M ^ 10)) =>
      M ^ 16 < h.valMinAbs.natAbs),
      ‖centeredProduct (squareD (M ^ 10)) p h.valMinAbs‖) < 1 / 2 := by
  have habs (h : ℤ) : (h.natAbs : ℝ) = |(h : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hbounded : ∀ h : ZMod (squareModulus (M ^ 10)),
      M ^ 16 < h.valMinAbs.natAbs → h.valMinAbs.natAbs ≤ M ^ 360 →
      ‖centeredProduct (squareD (M ^ 10)) p h.valMinAbs‖ ≤
        Real.exp (-κ * (M : ℝ) / 128) := by
    intro h hlo hhi
    have hloR : (M : ℝ) ^ 16 ≤ |(h.valMinAbs : ℝ)| := by
      rw [← habs]
      exact_mod_cast hlo.le
    have hhiR : |(h.valMinAbs : ℝ)| ≤ (M : ℝ) ^ 360 := by
      rw [← habs]
      exact_mod_cast hhi
    by_cases hbottom : 2 * |(h.valMinAbs : ℝ)| ≤ (M : ℝ) ^ 20
    · apply (bottom_frequency_centeredProduct_norm_le M hM p κ h.valMinAbs
        hp0 hp1 hκ0.le hκ hloR hbottom).trans
      apply Real.exp_le_exp.mpr
      have : 0 ≤ κ * (M : ℝ) := mul_nonneg hκ0.le (Nat.cast_nonneg M)
      linarith
    · apply (middle_frequency_norm_centeredProduct_le M hM p κ hp0 hp1 hκ0.le hκ
        h.valMinAbs (le_of_not_ge hbottom) hhiR).trans
      apply Real.exp_le_exp.mpr
      have hpower : (M : ℝ) ≤ (M : ℝ) ^ 9 :=
        le_self_pow₀ (by exact_mod_cast (show 1 ≤ M by omega)) (by decide)
      have := mul_le_mul_of_nonneg_left hpower hκ0.le
      linarith
  have hhigh : ∀ h : ZMod (squareModulus (M ^ 10)),
      M ^ 360 < h.valMinAbs.natAbs →
      ‖centeredProduct (squareD (M ^ 10)) p h.valMinAbs‖ ≤
        Real.exp (-8 * κ * highFrequencyConstant * (M : ℝ) ^ 51) := by
    intro h hh
    apply high_frequency_centeredProduct_norm_le M hM h.valMinAbs p κ
      hp0 hp1 hκ0.le hκ
    · rw [Int.abs_eq_natAbs]
      apply Int.ofNat_lt.mpr
      simpa only [← pow_mul] using hh
    · exact centered_frequency_abs_bound _ h
  have hsum := sum_norm_outside_small_le (squareModulus (M ^ 10)) (M ^ 16) (M ^ 360)
    (fun h => centeredProduct (squareD (M ^ 10)) p h.valMinAbs)
    (Real.exp (-κ * (M : ℝ) / 128))
    (Real.exp (-8 * κ * highFrequencyConstant * (M : ℝ) ^ 51))
    (Real.exp_pos _).le (Real.exp_pos _).le hbounded hhigh
  have hmod := squareModulus_mul_high_decay_le M hM κ hscale
  simp only [Nat.cast_pow] at hsum
  have hcount : (2 * (M : ℝ) ^ 360 + 1) * Real.exp (-κ * (M : ℝ) / 128) ≤
      (4 * (M : ℝ) ^ 360 + 2) * Real.exp (-κ * (M : ℝ) / 128) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have : (0 : ℝ) ≤ (M : ℝ) ^ 360 := by positivity
    linarith
  linarith

/-- The concrete square construction has sufficient centered Fourier mass. -/
theorem square_centered_fourier_sum_ge_half
    (M : ℕ) (hM : 262144 ≤ M) (p κ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hκ0 : 0 < κ) (hκ : κ ≤ p * (1 - p))
    (hscale : 121 ≤ 8 * κ * highFrequencyConstant * (M : ℝ) ^ 20)
    (htail : (4 * (M : ℝ) ^ 360 + 2) * Real.exp (-κ * (M : ℝ) / 128) +
      Real.exp (-(M : ℝ)) < 1 / 2) :
    (1 / 2 : ℝ) ≤ (∑ h : ZMod (squareModulus (M ^ 10)),
      centeredProduct (squareD (M ^ 10)) p h.valMinAbs).re := by
  classical
  let G := Finset.univ.filter (fun h : ZMod (squareModulus (M ^ 10)) =>
    h.valMinAbs.natAbs ≤ M ^ 16)
  apply real_sum_ge_half_of_good_bad Finset.univ G 0
    (fun h => centeredProduct (squareD (M ^ 10)) p h.valMinAbs)
    (Finset.subset_univ _) (by simp [G])
    (by simp [centeredProduct_zero])
  · intro h hh
    apply (small_frequency_centeredProduct_re_pos M (by omega) p hp0 hp1 h.valMinAbs _).le
    have hb := (Finset.mem_filter.mp hh).2
    have habs : (h.valMinAbs.natAbs : ℝ) = |(h.valMinAbs : ℝ)| := by
      simp only [Nat.cast_natAbs, Int.cast_abs]
    rw [← habs]
    exact_mod_cast hb
  · have hbad := square_sum_norm_outside_small_lt_half M hM p κ hp0 hp1 hκ0 hκ hscale htail
    have hsets : Finset.univ \ G = Finset.univ.filter
        (fun h : ZMod (squareModulus (M ^ 10)) => M ^ 16 < h.valMinAbs.natAbs) := by
      ext h
      simp [G]
    rw [hsets]
    exact hbad.le

end ReciprocalSquares
