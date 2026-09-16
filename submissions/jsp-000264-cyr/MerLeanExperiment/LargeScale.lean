import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace ReciprocalSquares

/-- The polynomial factor in the finite frequency count is dominated by the
exponential decay. -/
theorem frequency_tail_tendsto_zero (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => (4 * x ^ 360 + 2) * Real.exp (-κ * x / 128) +
      Real.exp (-x)) atTop (𝓝 0) := by
  have hphase (x : ℝ) : -(κ / 128) * x = -κ * x / 128 := by ring
  have h360 : Tendsto (fun x : ℝ => x ^ 360 * Real.exp (-κ * x / 128))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, hphase] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (360 : ℕ) (κ / 128)
        (by positivity)
  have hzero : Tendsto (fun x : ℝ => Real.exp (-κ * x / 128))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul, hphase] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (κ / 128) (by positivity)
  have hone : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 1 (by norm_num)
  convert ((h360.const_mul 4).add (hzero.const_mul 2)).add hone using 1
  · funext x
    ring
  · norm_num

/-- Choose the integer scale internally, satisfying all algebraic requirements
and the final finite frequency tail estimate at once. -/
theorem exists_large_scale (ε κ lam C : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hlam : 0 < lam) (hC : 0 < C) (B : ℕ) :
    ∃ M : ℕ, B ≤ M ∧ 262144 ≤ M ∧
      3 ≤ ε ^ 2 * (M : ℝ) ^ 10 ∧
      2904 ≤ lam * (M : ℝ) ^ 5 ∧
      121 ≤ 8 * κ * C * (M : ℝ) ^ 20 ∧
      (4 * (M : ℝ) ^ 360 + 2) * Real.exp (-κ * (M : ℝ) / 128) +
        Real.exp (-(M : ℝ)) < 1 / 2 := by
  have hcast : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have htail := ((frequency_tail_tendsto_zero κ hκ).comp hcast).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hall : ∀ᶠ M : ℕ in atTop, B ≤ M ∧ 262144 ≤ M ∧
      3 ≤ ε ^ 2 * (M : ℝ) ^ 10 ∧
      2904 ≤ lam * (M : ℝ) ^ 5 ∧
      121 ≤ 8 * κ * C * (M : ℝ) ^ 20 ∧
      (4 * (M : ℝ) ^ 360 + 2) * Real.exp (-κ * (M : ℝ) / 128) +
        Real.exp (-(M : ℝ)) < 1 / 2 := by
    filter_upwards [eventually_ge_atTop B, eventually_ge_atTop 262144,
      hcast.eventually (eventually_ge_atTop (3 / ε ^ 2)),
      hcast.eventually (eventually_ge_atTop (2904 / lam)),
      hcast.eventually (eventually_ge_atTop (121 / (8 * κ * C))), htail]
      with M hB hM hεM hlamM hκM htailM
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hpow10 : (M : ℝ) ≤ (M : ℝ) ^ 10 := le_self_pow₀ hMone (by decide)
    have hpow5 : (M : ℝ) ≤ (M : ℝ) ^ 5 := le_self_pow₀ hMone (by decide)
    have hpow20 : (M : ℝ) ≤ (M : ℝ) ^ 20 := le_self_pow₀ hMone (by decide)
    refine ⟨hB, hM, ?_, ?_, ?_, htailM⟩
    · have hbase := (div_le_iff₀ (sq_pos_of_pos hε)).mp hεM
      exact hbase.trans (by
        simpa only [mul_comm (M : ℝ)] using
          mul_le_mul_of_nonneg_left hpow10 (sq_nonneg ε))
    · have hbase := (div_le_iff₀ hlam).mp hlamM
      exact hbase.trans (by
        simpa only [mul_comm (M : ℝ)] using
          mul_le_mul_of_nonneg_left hpow5 hlam.le)
    · have hbase := (div_le_iff₀ (by positivity : 0 < 8 * κ * C)).mp hκM
      exact hbase.trans (by
        simpa only [mul_comm (M : ℝ)] using
          mul_le_mul_of_nonneg_left hpow20 (by positivity : 0 ≤ 8 * κ * C))
  exact hall.exists

end ReciprocalSquares
