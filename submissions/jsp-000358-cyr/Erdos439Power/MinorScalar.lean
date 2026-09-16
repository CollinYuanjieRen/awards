import Mathlib

open Filter
open scoped Topology

namespace Erdos439Power

noncomputable def minorScalarH (k M : ℕ) : ℝ :=
  ((M : ℝ) ^ 4) ^ (1 / 8 : ℝ) *
    (1 / (M : ℝ) + 1 / (M : ℝ) ^ 4) *
      (3 + 2 * Real.log ((M : ℝ) ^ (4 * k - 1)))

lemma minorScalarH_eq (k M : ℕ) (hM : 0 < M) :
    minorScalarH k M =
      (M : ℝ) ^ (1 / 2 : ℝ) *
        (1 / (M : ℝ) + 1 / (M : ℝ) ^ 4) *
          (3 + 2 * (4 * k - 1 : ℕ) * Real.log M) := by
  rw [minorScalarH]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hpow : ((M : ℝ) ^ 4) ^ (1 / 8 : ℝ) = (M : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hMr)]
    norm_num
  rw [hpow, Real.log_pow]
  ring

lemma minorScalar_power_identity (k M : ℕ) (hk : 1 ≤ k) :
    M ^ (4 * k - 1) * M = (M ^ 4) ^ ((k - 1) + 1) := by
  rw [← pow_succ, ← pow_mul]
  congr 1
  omega

/-- Exact normalization of the terminal expression used by the minor-arc
argument.  This lemma deliberately keeps the analytic estimates out of the
identity. -/
lemma terminalScalar_eq_normalized (D N b : ℝ) (d : ℕ)
    (hN : N ≠ 0) (hb : b ≠ 0) :
    D * (N ^ d / b + 1) * N + 2 * D * (N ^ d + b) * (1 + Real.log b) =
      (D * (1 / b + 1 / N ^ d +
        2 * (1 / N + b / N ^ (d + 1)) * (1 + Real.log b))) * N ^ (d + 1) := by
  field_simp
  ring

/-- The explicit terminal majorant is bounded by `minorScalarH`. -/
theorem minorScalar_terminal_bound (k M b : ℕ) (hk : 2 ≤ k)
    (hM : 2 ≤ M) (hMb : M < b) (hbQ : b ≤ M ^ (4 * k - 1)) :
    let N : ℝ := (M ^ 4 : ℕ)
    let d := k - 1
    let D : ℝ := N ^ (1 / 8 : ℝ)
    D * (N ^ d / b + 1) * N +
        2 * D * (N ^ d + b) * (1 + Real.log b) ≤
      minorScalarH k M * N ^ (d + 1) := by
  dsimp only
  let N : ℝ := (M ^ 4 : ℕ)
  let d := k - 1
  let D : ℝ := N ^ (1 / 8 : ℝ)
  have hM0 : 0 < M := by omega
  have hb0 : 0 < b := lt_trans hM0 hMb
  have hNr : (0 : ℝ) < N := by
    dsimp [N]
    positivity
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb0
  rw [terminalScalar_eq_normalized D N b d hNr.ne' hbr.ne']
  have hD : 0 ≤ D := Real.rpow_nonneg (le_of_lt hNr) _
  have hNpow : 0 ≤ N ^ (d + 1) := by positivity
  change (D * _) * N ^ (d + 1) ≤ minorScalarH k M * N ^ (d + 1)
  apply mul_le_mul_of_nonneg_right _ hNpow
  have hN1 : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 4 (by omega : M ≠ 0)))
  have hd1 : 1 ≤ d := by dsimp [d]; omega
  have hinvNd : 1 / N ^ d ≤ 1 / N := by
    rw [one_div, one_div]
    exact inv_anti₀ (lt_of_lt_of_le (by norm_num) hN1)
      (by simpa using pow_le_pow_right₀ hN1 hd1)
  have hinvb : (1 : ℝ) / b ≤ 1 / M := by
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hMb.le)
  have hQMr : (b : ℝ) / N ^ (d + 1) ≤ 1 / M := by
    have hcastQ : (b : ℝ) ≤ (M ^ (4 * k - 1) : ℕ) := by exact_mod_cast hbQ
    have hidNat := minorScalar_power_identity k M (by omega)
    have hid : ((M ^ (4 * k - 1) : ℕ) : ℝ) * M = N ^ (d + 1) := by
      simpa [N, d, Nat.cast_pow] using congrArg (fun n : ℕ => (n : ℝ)) hidNat
    calc
      (b : ℝ) / N ^ (d + 1) ≤
          (M ^ (4 * k - 1) : ℕ) / N ^ (d + 1) := by gcongr
      _ = 1 / M := by
        apply (div_eq_iff (pow_ne_zero _ hNr.ne')).2
        rw [← hid]
        field_simp
  have hinvN : 1 / N = 1 / (M : ℝ) ^ 4 := by
    congr 1
    norm_num [N]
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  have hlogQ : Real.log (b : ℝ) ≤ Real.log ((M : ℝ) ^ (4 * k - 1)) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact hbr
    · show (0 : ℝ) < (M : ℝ) ^ (4 * k - 1)
      exact pow_pos (by exact_mod_cast hM0) _
    · exact_mod_cast hbQ
  have hfac : 0 ≤ 1 + Real.log (b : ℝ) := by positivity
  have hsum :
      1 / (b : ℝ) + 1 / N ^ d +
          2 * (1 / N + b / N ^ (d + 1)) * (1 + Real.log b) ≤
        (1 / (M : ℝ) + 1 / (M : ℝ) ^ 4) *
          (3 + 2 * Real.log ((M : ℝ) ^ (4 * k - 1))) := by
    calc
      _ ≤ 1 / (M : ℝ) + 1 / N +
          2 * (1 / N + 1 / (M : ℝ)) * (1 + Real.log b) := by gcongr
      _ ≤ 1 / (M : ℝ) + 1 / N +
          2 * (1 / N + 1 / (M : ℝ)) *
            (1 + Real.log ((M : ℝ) ^ (4 * k - 1))) := by
              gcongr
      _ = _ := by rw [hinvN]; ring
  calc
    D * (1 / (b : ℝ) + 1 / N ^ d +
          2 * (1 / N + b / N ^ (d + 1)) * (1 + Real.log b)) ≤
        D * ((1 / (M : ℝ) + 1 / (M : ℝ) ^ 4) *
          (3 + 2 * Real.log ((M : ℝ) ^ (4 * k - 1)))) :=
      mul_le_mul_of_nonneg_left hsum hD
    _ = minorScalarH k M := by simp [minorScalarH, D, N, mul_assoc]

private lemma minorScalarH_nonneg (k M : ℕ) (hM : 2 ≤ M) :
    0 ≤ minorScalarH k M := by
  rw [minorScalarH]
  have hMr : (0 : ℝ) ≤ M := by positivity
  have hpow1 : (1 : ℝ) ≤ (M : ℝ) ^ (4 * k - 1) := by
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ M by omega))
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (add_nonneg (by positivity) (by positivity)))
    (add_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (Real.log_nonneg hpow1)))

private lemma minorScalarH_le (k M : ℕ) (hM : 2 ≤ M) :
    minorScalarH k M ≤
      2 * (3 + 2 * (4 * k - 1 : ℕ) * Real.log M) /
        (M : ℝ) ^ (1 / 2 : ℝ) := by
  rw [minorScalarH_eq k M (by omega)]
  let x : ℝ := M
  let s : ℝ := x ^ (1 / 2 : ℝ)
  have hx : 1 ≤ x := by
    change (1 : ℝ) ≤ (M : ℝ)
    exact_mod_cast (show 1 ≤ M by omega)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hs_sq : s * s = x := by
    dsimp [s]
    rw [← Real.rpow_add hx0]
    norm_num
  have hxpow : x ≤ x ^ 4 := by
    calc
      x = x * 1 := by ring
      _ ≤ x * x ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hx) (by positivity)
      _ = x ^ 4 := by ring
  have hinv : 1 / x ^ 4 ≤ 1 / x := one_div_le_one_div_of_le hx0 hxpow
  have hsmall : s * (1 / x + 1 / x ^ 4) ≤ 2 / s := by
    calc
      s * (1 / x + 1 / x ^ 4) ≤ s * (1 / x + 1 / x) := by gcongr
      _ = 2 / s := by field_simp; nlinarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  calc
    s * (1 / x + 1 / x ^ 4) *
        (3 + 2 * (4 * k - 1 : ℕ) * Real.log x) ≤
      (2 / s) * (3 + 2 * (4 * k - 1 : ℕ) * Real.log x) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = 2 * (3 + 2 * (4 * k - 1 : ℕ) * Real.log M) /
        (M : ℝ) ^ (1 / 2 : ℝ) := by simp [s, x]; ring

/-- For each fixed degree, the normalized scalar majorant tends to zero. -/
theorem tendsto_minorScalarH_atTop (k : ℕ) :
    Tendsto (minorScalarH k) atTop (𝓝 0) := by
  have hpow : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun M : ℕ => (6 : ℝ) / (M : ℝ) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hpow
  have hlog : Tendsto
      (fun M : ℕ => Real.log (M : ℝ) / (M : ℝ) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto
      (fun M : ℕ =>
        2 * (3 + 2 * (4 * k - 1 : ℕ) * Real.log M) /
          (M : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    convert hconst.add
      ((tendsto_const_nhds (x := (4 : ℝ) * ((4 * k - 1 : ℕ) : ℝ))).mul hlog)
        using 1
    · funext M
      ring
    · ring
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 2] with M hM
    exact minorScalarH_nonneg k M hM
  · filter_upwards [eventually_ge_atTop 2] with M hM
    exact minorScalarH_le k M hM
  · exact hupper

theorem eventually_minorScalarH_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, minorScalarH k M ≤ ε :=
  (tendsto_minorScalarH_atTop k).eventually_le_const hε

end Erdos439Power
