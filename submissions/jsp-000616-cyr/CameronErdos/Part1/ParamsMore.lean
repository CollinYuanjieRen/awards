import CameronErdos.Part1.Params
import CameronErdos.Part1.Granularization

/-!
# Side conditions of Green's Proposition 4 for the parameter choice of §3

`CameronErdos/Part1/Prop4.lean` proves Green's Proposition 4 under the hypotheses

* `0 < M`, `M < p`, `2 * L p M - 1 ≤ p`,
* `0 < ε`, `ε ≤ 1`, `24 ≤ ε * L p M`.

This file checks that Green's choice of parameters (`CameronErdos/Part1/Params.lean`),

* `ε = (log N)^{-1/11}`, `M = ⌊N exp(−(log N)^{1/12})⌋`, `L = ⌈p / M⌉`,

satisfies all of them, for all sufficiently large `N` and every `p ∈ [2N, 4N]`.

The only non-formal point is the last one: `L ≥ p / M ≥ 2N / (N exp(−(log N)^{1/12}))
= 2 exp((log N)^{1/12})`, so with `x = log N` it suffices that
`24 ≤ 2 x^{-1/11} exp(x^{1/12})`; the crude bound `exp y ≥ y²/4` with `y = x^{1/12}`
reduces this to `x^{5/66} ≥ 48`, which holds eventually since `1/6 − 1/11 = 5/66 > 0`.
-/

namespace CameronErdos

open Filter
open scoped Topology

noncomputable section

/-! ## Two elementary estimates -/

/-- `y²/4 ≤ exp y` for `y ≥ 0` (a crude consequence of `1 + y/2 ≤ exp (y/2)`). -/
theorem sq_div_four_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 / 4 ≤ Real.exp y := by
  have h : y / 2 + 1 ≤ Real.exp (y / 2) := Real.add_one_le_exp _
  have hpos : (0 : ℝ) < Real.exp (y / 2) := Real.exp_pos _
  have he : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith [h, hpos, hy]

/-- Variant of `two_le_MN_arg` with the lower bound `6`, which forces `MN N ≥ 3`. -/
theorem six_le_MN_arg {N : ℕ} (hN3 : 3 ≤ N)
    (hx6 : Real.log 6 + Real.log N ^ ((1 : ℝ) / 12) ≤ Real.log N) :
    (6 : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) := by
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hupos : (0 : ℝ) < Real.exp (Real.log N ^ ((1 : ℝ) / 12)) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hupos]
  calc (6 : ℝ) * Real.exp (Real.log N ^ ((1 : ℝ) / 12))
      = Real.exp (Real.log 6 + Real.log N ^ ((1 : ℝ) / 12)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.2 hx6
    _ = (N : ℝ) := Real.exp_log (by linarith)

/-- The three facts about `x = log N` that drive `eventually_prop4_side`. -/
theorem eventually_log_params4 :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ x ∧ Real.log 6 + x ^ ((1 : ℝ) / 12) ≤ x ∧ (48 : ℝ) ≤ x ^ ((5 : ℝ) / 66) := by
  have h1 := eventually_rpow_le_half 1 (show (1 : ℝ) / 12 < 1 by norm_num)
  have h3 := (tendsto_rpow_atTop (y := (5 : ℝ) / 66) (by norm_num)).eventually_ge_atTop 48
  filter_upwards [h1, h3, eventually_ge_atTop (2 * Real.log 6), eventually_ge_atTop (1 : ℝ)]
    with x hxa hxb hxc hxd
  exact ⟨hxd, by linarith, hxb⟩

/-- `L p (MN N)` is `LN N p`. -/
theorem L_MN (N p : ℕ) : L p (MN N) = LN N p := rfl

/-! ## The side conditions -/

/-- **The side conditions of `prop4_addTriples_le` for Green's parameters.**
For all large `N` and every `p ∈ [2N, 4N]`:
`0 < M`, `M < p`, `2L − 1 ≤ p`, `ε ≤ 1` and `24 ≤ ε L`. -/
theorem eventually_prop4_side :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 2 * N ≤ p → p ≤ 4 * N →
      0 < MN N ∧ MN N < p ∧ 2 * LN N p - 1 ≤ p ∧ epsN N ≤ 1 ∧
        (24 : ℝ) ≤ epsN N * (LN N p : ℝ) := by
  filter_upwards [eventually_ge_atTop 3, tendsto_log_nat.eventually eventually_log_params4]
    with N hN3 hxf
  obtain ⟨hx1, hx6, hx48⟩ := hxf
  intro p hp1 hp2
  have hN2 : 2 ≤ N := by omega
  have hx : (0 : ℝ) < Real.log N := log_natCast_pos hN2
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have htnn : (0 : ℝ) ≤ Real.log N ^ ((1 : ℝ) / 12) := Real.rpow_nonneg hx.le _
  -- `N exp(−(log N)^{1/12}) ≥ 6`, hence `M ≥ 3`
  have hy6 : (6 : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) :=
    six_le_MN_arg hN3 hx6
  have hMlow : (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) / 2 ≤ (MN N : ℝ) :=
    MN_lower (by linarith)
  have hM3 : (3 : ℝ) ≤ (MN N : ℝ) := by linarith
  have hMposR : (0 : ℝ) < (MN N : ℝ) := by linarith
  have hMpos : 0 < MN N := by exact_mod_cast hMposR
  -- (i) `M < p`
  have hMp : MN N < p := lt_of_le_of_lt (MN_le N) (by omega)
  have hp6 : 6 ≤ p := by omega
  have hp2N : (2 : ℝ) * (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  have hMN : (MN N : ℝ) ≤ (N : ℝ) := by exact_mod_cast MN_le N
  have hLnn : (0 : ℝ) ≤ (LN N p : ℝ) := Nat.cast_nonneg _
  -- (ii) `2L − 1 ≤ p`
  have hLlt : (LN N p : ℝ) < (p : ℝ) / (MN N : ℝ) + 1 := by
    rw [LN]; exact Nat.ceil_lt_add_one (by positivity)
  have hMne : (MN N : ℝ) ≠ 0 := ne_of_gt hMposR
  have hpM : (p : ℝ) / (MN N : ℝ) * (MN N : ℝ) = (p : ℝ) := by
    field_simp
  have hLM : (LN N p : ℝ) * (MN N : ℝ) < (p : ℝ) + (MN N : ℝ) := by
    have h := mul_lt_mul_of_pos_right hLlt hMposR
    rwa [add_mul, one_mul, hpM] at h
  have h3L : 3 * (LN N p : ℝ) ≤ (LN N p : ℝ) * (MN N : ℝ) := by
    nlinarith [hLnn, hM3]
  have h2LR : 2 * (LN N p : ℝ) ≤ (p : ℝ) := by linarith
  have h2L : 2 * LN N p ≤ p := by
    have : ((2 * LN N p : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  -- (iii) `ε ≤ 1`
  have heps1 : epsN N ≤ 1 := by
    rw [epsN]; exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hepspos : 0 < epsN N := epsN_pos hN2
  -- (iv) `24 ≤ ε L`
  have hMy : (MN N : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) := by
    rw [MN]; exact Nat.floor_le (by positivity)
  have hexpcancel : Real.exp (Real.log N ^ ((1 : ℝ) / 12)) *
      Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) = 1 := by
    rw [← Real.exp_add]; simp
  have hprod : 2 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) *
      ((N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12)))) = 2 * (N : ℝ) := by
    rw [show 2 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) *
          ((N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))))
        = 2 * (N : ℝ) * (Real.exp (Real.log N ^ ((1 : ℝ) / 12)) *
          Real.exp (-(Real.log N ^ ((1 : ℝ) / 12)))) from by ring, hexpcancel, mul_one]
  have h2exp : 2 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) * (MN N : ℝ) ≤ (p : ℝ) := by
    have h1 : 2 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) * (MN N : ℝ)
        ≤ 2 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) *
          ((N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12)))) :=
      mul_le_mul_of_nonneg_left hMy (by positivity)
    linarith
  have hceil : (p : ℝ) / (MN N : ℝ) ≤ (LN N p : ℝ) := by rw [LN]; exact Nat.le_ceil _
  have hLge : 2 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) ≤ (LN N p : ℝ) := by
    have h3 : 2 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) ≤ (p : ℝ) / (MN N : ℝ) := by
      rw [le_div_iff₀ hMposR]; exact h2exp
    linarith
  have ht2 : (Real.log N ^ ((1 : ℝ) / 12)) ^ (2 : ℕ) = Real.log N ^ ((1 : ℝ) / 6) := by
    rw [← Real.rpow_natCast (Real.log N ^ ((1 : ℝ) / 12)) 2, ← Real.rpow_mul hx.le]
    norm_num
  have hexpge : Real.log N ^ ((1 : ℝ) / 6) / 4
      ≤ Real.exp (Real.log N ^ ((1 : ℝ) / 12)) := by
    rw [← ht2]; exact sq_div_four_le_exp htnn
  have hLge2 : Real.log N ^ ((1 : ℝ) / 6) / 2 ≤ (LN N p : ℝ) := by linarith
  have hsplit : Real.log N ^ ((1 : ℝ) / 6)
      = Real.log N ^ ((1 : ℝ) / 11) * Real.log N ^ ((5 : ℝ) / 66) := by
    rw [← Real.rpow_add hx]; norm_num
  have hinv : epsN N * Real.log N ^ ((1 : ℝ) / 11) = 1 := by
    rw [epsN, ← Real.rpow_add hx, show -(1 / 11 : ℝ) + (1 : ℝ) / 11 = 0 by ring, Real.rpow_zero]
  have hkey : (24 : ℝ) ≤ epsN N * (LN N p : ℝ) := by
    have h1 : epsN N * (Real.log N ^ ((1 : ℝ) / 6) / 2) ≤ epsN N * (LN N p : ℝ) :=
      mul_le_mul_of_nonneg_left hLge2 hepspos.le
    have h2 : epsN N * (Real.log N ^ ((1 : ℝ) / 6) / 2)
        = Real.log N ^ ((5 : ℝ) / 66) / 2 := by
      rw [hsplit, show epsN N * (Real.log N ^ ((1 : ℝ) / 11) *
            Real.log N ^ ((5 : ℝ) / 66) / 2)
          = epsN N * Real.log N ^ ((1 : ℝ) / 11) * Real.log N ^ ((5 : ℝ) / 66) / 2 from by ring,
        hinv, one_mul]
    linarith
  exact ⟨hMpos, hMp, by omega, heps1, hkey⟩

/-- The same side conditions, phrased with `L p (MN N)` (which is `LN N p` by `rfl`) and with
the extra `0 < ε`, exactly as `prop4_addTriples_le` takes them. -/
theorem eventually_prop4_side' :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 2 * N ≤ p → p ≤ 4 * N → ∀ [NeZero p],
      0 < MN N ∧ MN N < p ∧ 2 * L p (MN N) - 1 ≤ p ∧ 0 < epsN N ∧ epsN N ≤ 1 ∧
        (24 : ℝ) ≤ epsN N * (L p (MN N) : ℝ) := by
  filter_upwards [eventually_prop4_side, eventually_ge_atTop 2] with N hN hN2
  intro p hp1 hp2 _
  obtain ⟨h1, h2, h3, h4, h5⟩ := hN p hp1 hp2
  rw [L_MN]
  exact ⟨h1, h2, h3, epsN_pos hN2, h4, h5⟩

end

/-! ## Axiom audit -/

#print axioms sq_div_four_le_exp
#print axioms six_le_MN_arg
#print axioms eventually_log_params4
#print axioms L_MN
#print axioms eventually_prop4_side
#print axioms eventually_prop4_side'

end CameronErdos
