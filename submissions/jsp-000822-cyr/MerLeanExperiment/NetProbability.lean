import MerLeanExperiment.FiniteProductTail

open MeasureTheory Set

namespace DiskDiscrepancy

/-- A finite family of bad events with total probability below one has a common avoider. -/
theorem exists_avoiding_finite_events {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype ι]
    (E : ι → Set Ω) {p : ℝ} (hE : ∀ i, μ.real (E i) ≤ p)
    (htotal : (Fintype.card ι : ℝ) * p < 1) : ∃ ω : Ω, ∀ i, ω ∉ E i := by
  by_contra hn
  push Not at hn
  have huniv : (⋃ i, E i) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hn ω
  have h := measureReal_iUnion_fintype_le (μ := μ) E
  have hsum : (∑ i, μ.real (E i)) ≤ (Fintype.card ι : ℝ) * p := by
    calc
      _ ≤ ∑ _i : ι, p := Finset.sum_le_sum fun i _ ↦ hE i
      _ = _ := by simp
  rw [huniv, probReal_univ] at h
  linarith

/-- The numerical union bound for the radius/centre grid used by the construction. -/
theorem polynomial_net_probability_lt_one {R N : ℝ} (hR : 4 ≤ R)
    (hN : N ≤ 400 * R ^ 6) : N * (2 / R ^ 15) < 1 := by
  have hR0 : 0 < R := by linarith
  have hpow : (4 : ℝ) ^ 9 ≤ R ^ 9 := pow_le_pow_left₀ (by norm_num) hR 9
  have hsmall : 800 / R ^ 9 < 1 := (div_lt_one (by positivity)).mpr (by norm_num at hpow ⊢; linarith)
  calc
    _ ≤ (400 * R ^ 6) * (2 / R ^ 15) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = 800 / R ^ 9 := by field_simp; ring
    _ < 1 := hsmall

/-- Hoeffding's exponential at the chosen boundary variance is inverse-polynomial. -/
theorem boundary_tail_numerical {R b : ℝ} (hR : 4 ≤ R) (hb : 0 < b)
    (hbR : b ≤ 120 * R) :
    2 * Real.exp (-2 * (30 * Real.sqrt (R * Real.log R)) ^ 2 / b) ≤ 2 / R ^ 15 := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt (mul_nonneg hR0.le hlog)
  have hexponent : -2 * (30 * Real.sqrt (R * Real.log R)) ^ 2 / b ≤ -15 * Real.log R := by
    apply (div_le_iff₀ hb).mpr
    have h := mul_le_mul_of_nonneg_right hbR hlog
    nlinarith [h]
  have hexp := Real.exp_le_exp.mpr hexponent
  have heq : Real.exp (-15 * Real.log R) = 1 / R ^ 15 := by
    rw [show -15 * Real.log R = -(15 * Real.log R) by ring, Real.exp_neg]
    rw [show (15 : ℝ) = (15 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hR0]
    simp only [one_div]
  rw [heq] at hexp
  calc
    _ ≤ 2 * (1 / R ^ 15) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = _ := by ring

end DiskDiscrepancy
