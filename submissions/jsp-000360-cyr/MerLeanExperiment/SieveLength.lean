import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace Erdos441

theorem sieve_cutoff_power_bound (M : ℕ) (hM : 3 ≤ M) (x : ℝ) (hx : 1 ≤ x) :
    (((2 * M)^⌊Real.log x / (8 * Real.log M)⌋₊ : ℕ) : ℝ) ≤
      x ^ (5 / 24 : ℝ) := by
  let z : ℕ := ⌊Real.log x / (8 * Real.log M)⌋₊
  have hMr : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hMr
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h8M : (8 : ℝ) ≤ (M : ℝ) ^ 2 := by
    have hMr3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [sq_nonneg ((M : ℝ) - 3)]
  have hlog8M := Real.strictMonoOn_log.monotoneOn
    (by norm_num : (0 : ℝ) < 8) (by positivity : (0 : ℝ) < (M : ℝ) ^ 2) h8M
  have hlog2M : 3 * Real.log 2 ≤ 2 * Real.log (M : ℝ) := by
    calc
      3 * Real.log 2 = Real.log (8 : ℝ) := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      _ ≤ Real.log ((M : ℝ) ^ 2) := hlog8M
      _ = 2 * Real.log (M : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogBase : Real.log ((2 * M : ℕ) : ℝ) ≤ (5 / 3 : ℝ) * Real.log M := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by positivity : (M : ℝ) ≠ 0)]
    nlinarith
  have hz : (z : ℝ) ≤ Real.log x / (8 * Real.log M) := by
    exact Nat.floor_le (div_nonneg hlogx (by positivity))
  have hlogpow : Real.log (((2 * M : ℕ) : ℝ)) * z ≤ Real.log x * (5 / 24 : ℝ) := by
    have hbaseNonneg : 0 ≤ Real.log (((2 * M : ℕ) : ℝ)) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * M by omega)
    calc
      Real.log (((2 * M : ℕ) : ℝ)) * z ≤
          Real.log (((2 * M : ℕ) : ℝ)) * (Real.log x / (8 * Real.log M)) :=
        mul_le_mul_of_nonneg_left hz hbaseNonneg
      _ ≤ ((5 / 3 : ℝ) * Real.log M) * (Real.log x / (8 * Real.log M)) :=
        mul_le_mul_of_nonneg_right hlogBase (div_nonneg hlogx (by positivity))
      _ = Real.log x * (5 / 24 : ℝ) := by field_simp; ring
  rw [show (((2 * M) ^ z : ℕ) : ℝ) = (((2 * M : ℕ) : ℝ) ^ z) by norm_cast]
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by linarith)]
  exact Real.exp_le_exp.mpr hlogpow

theorem eventually_sieve_length (M : ℕ) (hM : 3 ≤ M) (c0 : ℝ) (hc0 : 0 < c0) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (((2 * M)^⌊Real.log x / (8 * Real.log M)⌋₊ : ℕ) : ℝ) <
        c0 * x ^ (1 / 4 : ℝ) - 1 := by
  have ht24 := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 24)
  have ht4 := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have he24 : ∀ᶠ x : ℝ in Filter.atTop, 2 / c0 < x ^ (1 / 24 : ℝ) :=
    ht24.eventually (Filter.eventually_gt_atTop (2 / c0))
  have he4 : ∀ᶠ x : ℝ in Filter.atTop, 2 / c0 < x ^ (1 / 4 : ℝ) :=
    ht4.eventually (Filter.eventually_gt_atTop (2 / c0))
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), he24, he4] with x hx hx24 hx4
  have hbound := sieve_cutoff_power_bound M hM x hx
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hadd : x ^ (1 / 4 : ℝ) = x ^ (5 / 24 : ℝ) * x ^ (1 / 24 : ℝ) := by
    rw [← Real.rpow_add hxp]
    congr 1
    norm_num
  have hx5 : 0 < x ^ (5 / 24 : ℝ) := Real.rpow_pos_of_pos hxp _
  have hx24' : 2 < c0 * x ^ (1 / 24 : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hc0).mp hx24
  have hcprod : 2 * x ^ (5 / 24 : ℝ) < c0 * x ^ (1 / 4 : ℝ) := by
    rw [hadd]
    nlinarith [mul_lt_mul_of_pos_right hx24' hx5]
  have hc4 : 2 < c0 * x ^ (1 / 4 : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hc0).mp hx4
  nlinarith

end Erdos441
