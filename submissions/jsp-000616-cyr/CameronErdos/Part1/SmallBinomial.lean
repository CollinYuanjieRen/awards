import Mathlib
import CameronErdos.Part1.Params

/-!
# `Lem_SmallBinomial` — small binomial sums are subexponential

Green, *The Cameron–Erdős conjecture* (`ref/green-cameron-erdos-0304058.pdf`) needs, at several
places, that the number of subsets of `[N]` of size at most `γ N` is `2^{o(N)}` once `γ = γ(N)`
tends to `0`.  Quantitatively this is the classical entropy bound in the crude Chernoff form

`Σ_{j ≤ k} C(N, j) ≤ exp(γ N (1 + log(1/γ)))`   for `k ≤ γ N`, `0 < γ ≤ 1`,

together with `γ (1 + log(1/γ)) → 0` as `γ → 0⁺`.

This file proves:

* `sum_choose_le_exp` — the core tail bound, for any `N`, `k ≤ N` and any `0 < γ ≤ 1`
  with `k ≤ γ N`;
* `tendsto_mul_one_add_log_inv` — `γ (1 + log(1/γ)) → 0` as `γ → 0⁺`;
* `eventually_sum_choose_le_of_tendsto` — the packaged statement for an arbitrary eventually
  positive null sequence `γ N`;
* `eventually_small_binomial` — the special case `γ N = c · ε_N^{1/8}` used in Part 1;
* `eventually_family_bound_general` — the `θ`-general form of `Params.eventually_family_bound`.

`CameronErdos.Part1.Params` is imported (for `epsN`, `MN`, `epsN_tendsto_zero`, …) but is not
modified; the Chernoff-style helpers there are `private`, so the ones needed here are re-proved.
-/

namespace CameronErdos

open Finset Filter Topology

noncomputable section

/-! ## The core Chernoff bound -/

/-- Chernoff-style bound for binomial coefficients: for `0 < t ≤ 1` and `k ≤ N`,
`t^k · Σ_{j ≤ k} C(N, j) ≤ (1 + t)^N`.  (A copy of the `private` helper of
`CameronErdos.Part1.Params`, which is not accessible from here.) -/
private theorem pow_mul_sum_choose_le (N k : ℕ) (hk : k ≤ N) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ k * ∑ j ∈ range (k + 1), (N.choose j : ℝ) ≤ (1 + t) ^ N := by
  rw [Finset.mul_sum]
  have h2 : ∑ j ∈ range (k + 1), t ^ k * (N.choose j : ℝ)
      ≤ ∑ j ∈ range (k + 1), t ^ j * (N.choose j : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0.le ht1 hjk) (by positivity)
  have h3 : ∑ j ∈ range (k + 1), t ^ j * (N.choose j : ℝ)
      ≤ ∑ j ∈ range (N + 1), t ^ j * (N.choose j : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (Nat.succ_le_succ hk)) ?_
    intro i _ _
    positivity
  have h4 : (1 + t) ^ N = ∑ j ∈ range (N + 1), t ^ j * (N.choose j : ℝ) := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun j _ => by rw [one_pow, mul_one]
  linarith

/-- **Core tail bound.**  If `k ≤ N` and `k ≤ γ N` for some `0 < γ ≤ 1`, then
`Σ_{j ≤ k} C(N, j) ≤ exp(γ N (1 + log(1/γ)))`. -/
theorem sum_choose_le_exp {N k : ℕ} (hk : k ≤ N) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hkγ : (k : ℝ) ≤ γ * N) :
    ∑ j ∈ range (k + 1), (N.choose j : ℝ) ≤ Real.exp (γ * N * (1 + Real.log (1 / γ))) := by
  have hmul := pow_mul_sum_choose_le N k hk hγ0 hγ1
  -- `(1 + γ)^N ≤ exp(γ N)`
  have hexp : (1 + γ) ^ N ≤ Real.exp (γ * N) := by
    calc (1 + γ) ^ N ≤ Real.exp γ ^ N := by
          gcongr
          linarith [Real.add_one_le_exp γ]
      _ = Real.exp ((N : ℝ) * γ) := (Real.exp_nat_mul γ N).symm
      _ = Real.exp (γ * N) := by rw [mul_comm]
  have hpowpos : (0 : ℝ) < γ ^ k := by positivity
  have hS : (∑ j ∈ range (k + 1), (N.choose j : ℝ)) * γ ^ k ≤ Real.exp (γ * N) := by
    calc (∑ j ∈ range (k + 1), (N.choose j : ℝ)) * γ ^ k
        = γ ^ k * ∑ j ∈ range (k + 1), (N.choose j : ℝ) := mul_comm _ _
      _ ≤ (1 + γ) ^ N := hmul
      _ ≤ Real.exp (γ * N) := hexp
  rw [← le_div_iff₀ hpowpos] at hS
  have hγk : Real.exp ((k : ℝ) * Real.log γ) = γ ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hγ0]
  have hdiv : Real.exp (γ * N) / γ ^ k = Real.exp (γ * N - (k : ℝ) * Real.log γ) := by
    rw [Real.exp_sub, hγk]
  rw [hdiv] at hS
  refine hS.trans (Real.exp_le_exp.2 ?_)
  have hlog : Real.log (1 / γ) = -Real.log γ := by rw [one_div, Real.log_inv]
  have hlognonpos : Real.log γ ≤ 0 := Real.log_nonpos hγ0.le hγ1
  have hprod : 0 ≤ (γ * N - (k : ℝ)) * (-Real.log γ) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hlog]
  nlinarith [hprod]

/-! ## The entropy factor vanishes -/

/-- `γ (1 + log(1/γ)) → 0` as `γ → 0⁺`. -/
theorem tendsto_mul_one_add_log_inv :
    Tendsto (fun γ : ℝ => γ * (1 + Real.log (1 / γ))) (𝓝[>] 0) (𝓝 0) := by
  have hfun : (fun γ : ℝ => γ * (1 + Real.log (1 / γ))) = fun γ : ℝ => γ - γ * Real.log γ := by
    funext γ
    rw [one_div, Real.log_inv]
    ring
  have hcont : Continuous fun γ : ℝ => γ * (1 + Real.log (1 / γ)) := by
    rw [hfun]
    exact continuous_id.sub Real.continuous_mul_log
  have h : Tendsto (fun γ : ℝ => γ * (1 + Real.log (1 / γ))) (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto 0
  exact h.mono_left nhdsWithin_le_nhds

/-! ## The packaged statement for a null sequence of ratios -/

/-- If `γ N → 0` (and `γ N > 0` eventually), then for every `θ > 0` and all large `N`, every
`k ≤ γ N · N` satisfies `Σ_{j ≤ k} C(N, j) ≤ 2^{θ N}`. -/
theorem eventually_sum_choose_le_of_tendsto {γ : ℕ → ℝ} (hγ : Tendsto γ atTop (𝓝 0))
    (hpos : ∀ᶠ N : ℕ in atTop, 0 < γ N) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ γ N * N →
      ∑ j ∈ range (k + 1), (N.choose j : ℝ) ≤ (2 : ℝ) ^ (θ * N) := by
  have hmem : ∀ᶠ N : ℕ in atTop, γ N ∈ Set.Ioi (0 : ℝ) := hpos
  have hγ' : Tendsto γ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within γ hγ hmem
  have hent : Tendsto (fun N : ℕ => γ N * (1 + Real.log (1 / γ N))) atTop (𝓝 0) :=
    tendsto_mul_one_add_log_inv.comp hγ'
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall : ∀ᶠ N : ℕ in atTop, γ N * (1 + Real.log (1 / γ N)) ≤ θ * Real.log 2 :=
    hent.eventually_le_const (by positivity)
  have hle1 : ∀ᶠ N : ℕ in atTop, γ N ≤ 1 := hγ.eventually_le_const (by norm_num)
  filter_upwards [hpos, hsmall, hle1] with N hγN hentN hγ1 k hk
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hkN : k ≤ N := by
    have h1 : (k : ℝ) ≤ (N : ℝ) := by nlinarith
    exact_mod_cast h1
  have hmain := sum_choose_le_exp hkN hγN hγ1 hk
  refine hmain.trans ?_
  have hexpo : γ N * N * (1 + Real.log (1 / γ N)) ≤ Real.log 2 * (θ * N) := by
    have h := mul_le_mul_of_nonneg_right hentN hN0
    calc γ N * N * (1 + Real.log (1 / γ N))
        = γ N * (1 + Real.log (1 / γ N)) * N := by ring
      _ ≤ θ * Real.log 2 * N := h
      _ = Real.log 2 * (θ * N) := by ring
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.2 hexpo

/-! ## Small binomial sums: `k ≤ c ε^{1/8} N` -/

/-- **`Lem_SmallBinomial`.**  For every `c, θ > 0` and all large `N`, every `k` with
`k ≤ c · ε_N^{1/8} · N` satisfies `Σ_{j ≤ k} C(N, j) ≤ 2^{θ N}`.  (`ε^{1/8}` is written as a
triple square root, matching the rest of the library.) -/
theorem eventually_small_binomial (c θ : ℝ) (hc : 0 < c) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ c * Real.sqrt (Real.sqrt (Real.sqrt (epsN N))) * N →
        ∑ j ∈ range (k + 1), (N.choose j : ℝ) ≤ (2 : ℝ) ^ (θ * N) := by
  set γ : ℕ → ℝ := fun N => c * Real.sqrt (Real.sqrt (Real.sqrt (epsN N))) with hγdef
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt (Real.sqrt (epsN N)))) atTop (𝓝 0) := by
    have h := epsN_tendsto_zero.sqrt.sqrt.sqrt
    simpa using h
  have hγ : Tendsto γ atTop (𝓝 0) := by
    have := hroot.const_mul c
    simpa [hγdef] using this
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < γ N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have h1 : 0 < epsN N := epsN_pos hN
    have h2 : 0 < Real.sqrt (Real.sqrt (Real.sqrt (epsN N))) :=
      Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 h1))
    exact mul_pos hc h2
  exact eventually_sum_choose_le_of_tendsto hγ hpos θ hθ

/-! ## Auxiliary growth estimates -/

/-- `x^2/4 ≤ exp x` for `x ≥ 0`. -/
private theorem sq_div_four_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 / 4 ≤ Real.exp x := by
  have h1 : x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
  have h2 : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [Real.exp_pos (x / 2)]

/-- Any linear function is eventually dominated by `2^{bN}`, `b > 0`. -/
private theorem eventually_linear_le_rpow_two (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, a * N ≤ (2 : ℝ) ^ (b * N) := by
  set c : ℝ := Real.log 2 * b with hcdef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by positivity
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually_ge_atTop (4 * a / c ^ 2), hcast.eventually_ge_atTop 0]
    with N hN hN0
  have hkey : 4 * a ≤ c ^ 2 * N := by
    rw [div_le_iff₀ (by positivity)] at hN
    linarith
  have hquad : a * N ≤ (c * N) ^ 2 / 4 := by nlinarith
  have hexp : (c * N) ^ 2 / 4 ≤ Real.exp (c * N) :=
    sq_div_four_le_exp (by positivity)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have : Real.log 2 * (b * N) = c * N := by rw [hcdef]; ring
  rw [this]
  linarith

/-- `exp(-(x^{1/12})) ≤ δ` for all large `x`. -/
private theorem eventually_exp_neg_rpow_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-(x ^ ((1 : ℝ) / 12))) ≤ δ := by
  filter_upwards [(tendsto_rpow_atTop (y := (1 : ℝ) / 12)
    (by norm_num)).eventually_ge_atTop (Real.log (1 / δ))] with x hx
  calc Real.exp (-(x ^ ((1 : ℝ) / 12))) ≤ Real.exp (-Real.log (1 / δ)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = δ := by
        rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]

/-! ## The `θ`-general family bound -/

/-- **`Lem_SmallBinomial`, family form.**  The `θ`-general version of
`CameronErdos.eventually_family_bound`: for every `θ > 0` and all large `N`,
`p · 2^{M} · Σ_{j ≤ ε p} C(N, j) ≤ 2^{θ N}` for every `p ∈ [2N, 4N]`. -/
theorem eventually_family_bound_general (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 2 * N ≤ p → p ≤ 4 * N →
      (p : ℝ) * 2 ^ (MN N) * (∑ j ∈ range (⌊epsN N * (p : ℝ)⌋₊ + 1), (N.choose j : ℝ))
        ≤ (2 : ℝ) ^ (θ * N) := by
  -- the binomial factor, with `γ N = 4 ε_N`
  have hγ : Tendsto (fun N : ℕ => 4 * epsN N) atTop (𝓝 0) := by
    simpa using epsN_tendsto_zero.const_mul (4 : ℝ)
  have hγpos : ∀ᶠ N : ℕ in atTop, 0 < 4 * epsN N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have h := epsN_pos hN
    linarith
  have hbin := eventually_sum_choose_le_of_tendsto hγ hγpos (θ / 2) (by positivity)
  -- the factor `p ≤ 4 N`
  have hlin := eventually_linear_le_rpow_two (4 : ℝ) (show (0 : ℝ) < θ / 4 by positivity)
  -- the factor `2^M`
  have hMsmall : ∀ᶠ N : ℕ in atTop,
      Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) ≤ θ / 4 :=
    tendsto_log_nat.eventually (eventually_exp_neg_rpow_le (show (0 : ℝ) < θ / 4 by positivity))
  filter_upwards [hbin, hlin, hMsmall, eventually_ge_atTop 2] with N hbinN hlinN hMN hN2
  intro p hp1 hp2
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hεpos : 0 < epsN N := epsN_pos hN2
  have hpR : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hp2
  -- factor 1
  have hf1 : (p : ℝ) ≤ (2 : ℝ) ^ (θ / 4 * (N : ℝ)) := hpR.trans hlinN
  -- factor 2
  have hMle : (MN N : ℝ) ≤ θ / 4 * (N : ℝ) := by
    have h1 : (MN N : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) := by
      rw [MN]; exact Nat.floor_le (by positivity)
    nlinarith
  have hf2 : (2 : ℝ) ^ (MN N) ≤ (2 : ℝ) ^ (θ / 4 * (N : ℝ)) := by
    rw [show ((2 : ℝ) ^ (MN N)) = (2 : ℝ) ^ ((MN N : ℕ) : ℝ) from (Real.rpow_natCast 2 _).symm]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hMle
  -- factor 3
  have hk : (⌊epsN N * (p : ℝ)⌋₊ : ℝ) ≤ 4 * epsN N * (N : ℝ) := by
    have h1 : (⌊epsN N * (p : ℝ)⌋₊ : ℝ) ≤ epsN N * (p : ℝ) := Nat.floor_le (by positivity)
    nlinarith
  have hf3 : (∑ j ∈ range (⌊epsN N * (p : ℝ)⌋₊ + 1), (N.choose j : ℝ))
      ≤ (2 : ℝ) ^ (θ / 2 * (N : ℝ)) := hbinN _ hk
  -- combine
  have hprod : (2 : ℝ) ^ (θ / 4 * (N : ℝ)) * (2 : ℝ) ^ (θ / 4 * (N : ℝ)) *
      (2 : ℝ) ^ (θ / 2 * (N : ℝ)) = (2 : ℝ) ^ (θ * (N : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  calc (p : ℝ) * 2 ^ (MN N) * (∑ j ∈ range (⌊epsN N * (p : ℝ)⌋₊ + 1), (N.choose j : ℝ))
      ≤ (2 : ℝ) ^ (θ / 4 * (N : ℝ)) * (2 : ℝ) ^ (θ / 4 * (N : ℝ)) *
        (2 : ℝ) ^ (θ / 2 * (N : ℝ)) := by
        refine mul_le_mul (mul_le_mul hf1 hf2 (by positivity) (by positivity)) hf3
          (Finset.sum_nonneg fun j _ => by positivity) (by positivity)
    _ = (2 : ℝ) ^ (θ * (N : ℝ)) := hprod

end

/-! ## Axiom audit -/

#print axioms pow_mul_sum_choose_le
#print axioms sum_choose_le_exp
#print axioms tendsto_mul_one_add_log_inv
#print axioms eventually_sum_choose_le_of_tendsto
#print axioms eventually_small_binomial
#print axioms sq_div_four_le_exp
#print axioms eventually_linear_le_rpow_two
#print axioms eventually_exp_neg_rpow_le
#print axioms eventually_family_bound_general

end CameronErdos
