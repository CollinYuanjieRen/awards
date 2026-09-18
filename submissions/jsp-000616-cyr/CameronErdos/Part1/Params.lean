import Mathlib
import CameronErdos.Statement

/-!
# `Lem_ParamChoice` — the parameter choice of Green (2004), §3

Green, *The Cameron–Erdős conjecture* (arXiv math/0304058, p. 7):

> It is an easy but slightly tedious task to check that if we put `ε = (log N)^{-1/11}` and
> `M = ⌊N exp(−(log N)^{1/12})⌋` then, at least for `N` sufficiently large, `A` has at least
> one good length.

This file is pure real analysis: it introduces the parameters

* `epsN N = (log N)^{-1/11}`,
* `MN N  = ⌊N exp(−(log N)^{1/12})⌋`,
* `LN N p = ⌈p / MN N⌉`  (`p` a prime in `[2N, 4N]`),

and the Proposition 5 exponent `E N = 256 ε₁^{-4} ε₂^{-2} ε₃^{-1}` for
`ε₁ = ε`, `ε₂ = ε²/144`, `ε₃ = ε²/80` (the factor `α²` of Proposition 5 is absorbed,
since `α ≤ 1`), and proves the two eventual estimates that Proposition 6 needs:

* `eventually_prop5_hypothesis` : `(4 L)^{E N} < p` for every `p ∈ [2N, 4N]`,
* `eventually_family_bound` : `p · 2^{M} · Σ_{j ≤ εp} C(N, j) ≤ 2^{N/240}`.

Both are stated with `∀ᶠ N in atTop` (existential thresholds `N₀`, `N₁`, as in the source).
-/

namespace CameronErdos

open Filter Finset
open scoped Topology

noncomputable section

/-! ## The parameters -/

/-- Green's `ε = (log N)^{-1/11}`. -/
def epsN (N : ℕ) : ℝ := Real.log N ^ (-(1 / 11) : ℝ)

/-- Green's `M = ⌊N exp(−(log N)^{1/12})⌋`. -/
def MN (N : ℕ) : ℕ := ⌊(N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12)))⌋₊

/-- The number of progressions of common difference `d` in `ZMod p`, `L = ⌈p / M⌉`. -/
def LN (N p : ℕ) : ℕ := ⌈(p : ℝ) / (MN N : ℝ)⌉₊

/-- `ε₁ = ε`. -/
def eps1 (N : ℕ) : ℝ := epsN N

/-- `ε₂ = ε² / 144`. -/
def eps2 (N : ℕ) : ℝ := epsN N ^ 2 / 144

/-- `ε₃ = ε² / 80`. -/
def eps3 (N : ℕ) : ℝ := epsN N ^ 2 / 80

/-- The exponent `256 α² ε₁^{-4} ε₂^{-2} ε₃^{-1}` of Green's Proposition 5, with `α ≤ 1`
absorbed (`α² ≤ 1`). -/
def E (N : ℕ) : ℝ := 256 * eps1 N ^ (-4 : ℤ) * eps2 N ^ (-2 : ℤ) * eps3 N ^ (-1 : ℤ)

/-! ## Elementary facts about the parameters -/

theorem log_natCast_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Real.log N := by
  have h : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  exact Real.log_pos h

theorem epsN_pos {N : ℕ} (hN : 2 ≤ N) : 0 < epsN N :=
  Real.rpow_pos_of_pos (log_natCast_pos hN) _

theorem epsN_tendsto_zero : Tendsto (fun N : ℕ => epsN N) atTop (nhds 0) := by
  have h : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_atTop (y := 1 / 11) (by norm_num)).comp h

theorem MN_le (N : ℕ) : MN N ≤ N := by
  have h0 : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  have h1 : Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg h0 _))
  have h2 : (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) ≤ (N : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N, Real.exp_pos (-(Real.log N ^ ((1 : ℝ) / 12)))]
  have h3 := Nat.floor_le_floor h2
  simpa [MN] using h3

theorem LN_ge_one {N p : ℕ} (hM : 0 < MN N) (hp : 0 < p) : 1 ≤ LN N p := by
  have : (0 : ℝ) < (p : ℝ) / (MN N : ℝ) :=
    div_pos (by exact_mod_cast hp) (by exact_mod_cast hM)
  simpa [LN] using Nat.one_le_ceil_iff.2 this

/-- `E N = 256 · 144² · 80 · ε^{-10} = 424673280 · (log N)^{10/11}`. -/
theorem E_eq {N : ℕ} (hN : 2 ≤ N) : E N = 424673280 * Real.log N ^ ((10 : ℝ) / 11) := by
  have hx : 0 < Real.log N := log_natCast_pos hN
  have hε : 0 < epsN N := epsN_pos hN
  have hεne : epsN N ≠ 0 := ne_of_gt hε
  have h10 : epsN N ^ (10 : ℕ) = (Real.log N ^ ((10 : ℝ) / 11))⁻¹ := by
    rw [epsN, ← Real.rpow_natCast (Real.log N ^ (-(1 / 11) : ℝ)) 10, ← Real.rpow_mul hx.le,
      show (-(1 / 11 : ℝ)) * ((10 : ℕ) : ℝ) = -((10 : ℝ) / 11) by push_cast; ring,
      Real.rpow_neg hx.le]
  have hE : E N = 424673280 * (epsN N ^ (10 : ℕ))⁻¹ := by
    simp only [E, eps1, eps2, eps3, zpow_neg, zpow_one]
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, show ((4 : ℤ)) = ((4 : ℕ) : ℤ) from rfl,
      zpow_natCast, zpow_natCast]
    field_simp
    ring
  rw [hE, h10, inv_inv]

/-! ## Asymptotic helpers -/

/-- For any `c` and any exponent `a < 1`, eventually `c * x ^ a ≤ x / 2`. -/
theorem eventually_rpow_le_half (c : ℝ) {a : ℝ} (ha : a < 1) :
    ∀ᶠ x : ℝ in atTop, c * x ^ a ≤ x / 2 := by
  have h0 : Tendsto (fun x : ℝ => x ^ (a - 1)) atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (y := 1 - a) (by linarith)
    simpa [show -(1 - a) = a - 1 by ring] using h
  have h1 : Tendsto (fun x : ℝ => c * x ^ (a - 1)) atTop (nhds 0) := by
    simpa using h0.const_mul c
  have h2 : ∀ᶠ x : ℝ in atTop, c * x ^ (a - 1) ≤ 1 / 2 :=
    h1.eventually_le_const (by norm_num)
  filter_upwards [h2, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hxa : x ^ a = x ^ (a - 1) * x := by
    have h := Real.rpow_add hx0 (a - 1) 1
    rw [Real.rpow_one, show a - 1 + 1 = a by ring] at h
    exact h
  calc c * x ^ a = c * x ^ (a - 1) * x := by rw [hxa]; ring
    _ ≤ 1 / 2 * x := mul_le_mul_of_nonneg_right hx hx0.le
    _ = x / 2 := by ring

theorem log_le_two_rpow {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * x ^ ((1 : ℝ) / 2) := by
  have hs : (0 : ℝ) < x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  have h1 : Real.log (x ^ ((1 : ℝ) / 2)) = 1 / 2 * Real.log x := Real.log_rpow hx _
  have h2 : Real.log (x ^ ((1 : ℝ) / 2)) ≤ x ^ ((1 : ℝ) / 2) - 1 := Real.log_le_sub_one_of_pos hs
  linarith

/-- `log` is eventually below any positive multiple of the identity. -/
private theorem eventually_log_le (d : ℝ) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ d * x := by
  filter_upwards [eventually_rpow_le_half (2 / d) (show (1 : ℝ) / 2 < 1 by norm_num),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have h := log_le_two_rpow hx0
  have h2 : 2 * x ^ ((1 : ℝ) / 2) ≤ d * x / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hx hd.le
    calc 2 * x ^ ((1 : ℝ) / 2) = d * (2 / d * x ^ ((1 : ℝ) / 2)) := by
          field_simp
      _ ≤ d * (x / 2) := hmul
      _ = d * x / 2 := by ring
  nlinarith

/-- The three facts about `x = log N` that drive `eventually_prop5_hypothesis`.
The third one is the inequality `C₀ x^{10/11} (log 36 + x^{1/12}) ≤ x`, which holds because
`10/11 + 1/12 = 131/132 < 1`. -/
private theorem eventually_log_params :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ x ∧ Real.log 2 + x ^ ((1 : ℝ) / 12) ≤ x ∧
        424673280 * x ^ ((10 : ℝ) / 11) * (Real.log 36 + x ^ ((1 : ℝ) / 12)) ≤ x := by
  have h1 := eventually_rpow_le_half 1 (show (1 : ℝ) / 12 < 1 by norm_num)
  have h2 := eventually_rpow_le_half (424673280 * Real.log 36)
    (show (10 : ℝ) / 11 < 1 by norm_num)
  have h3 := eventually_rpow_le_half (424673280 : ℝ) (show (131 : ℝ) / 132 < 1 by norm_num)
  filter_upwards [h1, h2, h3, eventually_ge_atTop (2 * Real.log 2), eventually_ge_atTop (1 : ℝ)]
    with x hx1 hx2 hx3 hx4 hx5
  have hxpos : (0 : ℝ) < x := by linarith
  refine ⟨hx5, by linarith, ?_⟩
  have hprod : x ^ ((10 : ℝ) / 11) * x ^ ((1 : ℝ) / 12) = x ^ ((131 : ℝ) / 132) := by
    rw [← Real.rpow_add hxpos]; norm_num
  calc 424673280 * x ^ ((10 : ℝ) / 11) * (Real.log 36 + x ^ ((1 : ℝ) / 12))
      = 424673280 * Real.log 36 * x ^ ((10 : ℝ) / 11) + 424673280 * x ^ ((131 : ℝ) / 132) := by
        rw [← hprod]; ring
    _ ≤ x / 2 + x / 2 := add_le_add hx2 hx3
    _ = x := by ring

theorem tendsto_log_nat : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-! ## `M` is positive and comparable to `N exp(-(log N)^{1/12})` -/

theorem two_le_MN_arg {N : ℕ} (hN3 : 3 ≤ N)
    (hx2 : Real.log 2 + Real.log N ^ ((1 : ℝ) / 12) ≤ Real.log N) :
    (2 : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) := by
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hxpos : (0 : ℝ) < Real.log N := log_natCast_pos (by omega)
  have hupos : (0 : ℝ) < Real.exp (Real.log N ^ ((1 : ℝ) / 12)) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hupos]
  calc (2 : ℝ) * Real.exp (Real.log N ^ ((1 : ℝ) / 12))
      = Real.exp (Real.log 2 + Real.log N ^ ((1 : ℝ) / 12)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.2 hx2
    _ = (N : ℝ) := Real.exp_log (by linarith)

theorem MN_lower {N : ℕ}
    (h : (2 : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12)))) :
    (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) / 2 ≤ (MN N : ℝ) := by
  have hfl := Nat.sub_one_lt_floor ((N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))))
  rw [MN]
  linarith

/-- `M > 0` for all large `N`. -/
theorem eventually_MN_pos : ∀ᶠ N : ℕ in atTop, 0 < MN N := by
  filter_upwards [eventually_ge_atTop 3, tendsto_log_nat.eventually eventually_log_params]
    with N hN3 hxf
  obtain ⟨-, hx2, -⟩ := hxf
  have h := two_le_MN_arg hN3 hx2
  have hlow := MN_lower h
  have : (0 : ℝ) < (MN N : ℝ) := by linarith
  exact_mod_cast this

/-! ## Part 1: the hypothesis of Green's Proposition 5 -/

/-- **`Lem_ParamChoice`, first half.**  For all large `N` and every `p ∈ [2N, 4N]`,
`(4 L)^{E} < p`, where `L = ⌈p / M⌉` and `E = 256 ε₁^{-4} ε₂^{-2} ε₃^{-1}`.  This is exactly
the hypothesis of Green's Proposition 5 (with `α ≤ 1`), so `A` has a good length. -/
theorem eventually_prop5_hypothesis :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 2 * N ≤ p → p ≤ 4 * N →
      (4 * (LN N p : ℝ)) ^ (E N) < (p : ℝ) := by
  filter_upwards [eventually_ge_atTop 3, tendsto_log_nat.eventually eventually_log_params]
    with N hN3 hxf
  obtain ⟨hx1, hx2, hx3⟩ := hxf
  intro p hp1 hp2
  have hN2 : 2 ≤ N := by omega
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hxpos : (0 : ℝ) < Real.log N := log_natCast_pos hN2
  have hupos : (0 : ℝ) < Real.exp (Real.log N ^ ((1 : ℝ) / 12)) := Real.exp_pos _
  have hu1 : (1 : ℝ) ≤ Real.exp (Real.log N ^ ((1 : ℝ) / 12)) :=
    Real.one_le_exp (Real.rpow_nonneg hxpos.le _)
  have hT2 := two_le_MN_arg hN3 hx2
  have hMlow := MN_lower hT2
  have hMpos : (0 : ℝ) < (MN N : ℝ) := by linarith
  have hMposN : 0 < MN N := by exact_mod_cast hMpos
  have hppos : 0 < p := by omega
  have hpR : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hp2
  -- `L ≤ 9 exp((log N)^{1/12})`
  have hLlt : (LN N p : ℝ) < (p : ℝ) / (MN N : ℝ) + 1 := by
    rw [LN]; exact Nat.ceil_lt_add_one (by positivity)
  have hdiv : (p : ℝ) / (MN N : ℝ) ≤ 8 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) := by
    rw [div_le_iff₀ hMpos]
    have h8 : 8 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) *
        ((N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) / 2) = 4 * (N : ℝ) := by
      rw [Real.exp_neg]; field_simp; norm_num
    have key := mul_le_mul_of_nonneg_left hMlow
      (show (0 : ℝ) ≤ 8 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) by positivity)
    rw [h8] at key
    linarith
  have hLle : (LN N p : ℝ) ≤ 9 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) := by linarith
  have hL1R : (1 : ℝ) ≤ (LN N p : ℝ) := by exact_mod_cast LN_ge_one hMposN hppos
  have h4Lpos : (0 : ℝ) < 4 * (LN N p : ℝ) := by linarith
  -- `log (4 L) ≤ log 36 + (log N)^{1/12}`
  have hlog4L : Real.log (4 * (LN N p : ℝ)) ≤ Real.log 36 + Real.log N ^ ((1 : ℝ) / 12) := by
    have h1 : 4 * (LN N p : ℝ) ≤ 36 * Real.exp (Real.log N ^ ((1 : ℝ) / 12)) := by linarith
    have h2 := Real.log_le_log h4Lpos h1
    rwa [Real.log_mul (by norm_num) (ne_of_gt hupos), Real.log_exp] at h2
  -- the exponent
  have hEeq : E N = 424673280 * Real.log N ^ ((10 : ℝ) / 11) := E_eq hN2
  have hEnn : 0 ≤ E N := by
    rw [hEeq]; positivity
  have hkey : Real.log (4 * (LN N p : ℝ)) * E N ≤ Real.log N := by
    have h1 : Real.log (4 * (LN N p : ℝ)) * E N
        ≤ (Real.log 36 + Real.log N ^ ((1 : ℝ) / 12)) * E N :=
      mul_le_mul_of_nonneg_right hlog4L hEnn
    have h2 : (Real.log 36 + Real.log N ^ ((1 : ℝ) / 12)) * E N
        = 424673280 * Real.log N ^ ((10 : ℝ) / 11) *
          (Real.log 36 + Real.log N ^ ((1 : ℝ) / 12)) := by
      rw [hEeq]; ring
    rw [h2] at h1
    linarith
  rw [Real.rpow_def_of_pos h4Lpos]
  have h1 : Real.exp (Real.log (4 * (LN N p : ℝ)) * E N) ≤ Real.exp (Real.log N) :=
    Real.exp_le_exp.2 hkey
  have h2 : Real.exp (Real.log N) = (N : ℝ) := Real.exp_log (by linarith)
  have h3 : (2 : ℝ) * (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  linarith


/-! ## Part 2: the size of the family `F` -/

/-- Chernoff-style tail bound for binomial coefficients: for `0 < t ≤ 1`,
`t^k · Σ_{j ≤ k} C(N, j) ≤ (1 + t)^N`. -/
private theorem sum_choose_mul_le (N k : ℕ) (hk : k ≤ N) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
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
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.succ_le_succ hk)) ?_
    intro i _ _
    positivity
  have h4 : (1 + t) ^ N = ∑ j ∈ range (N + 1), t ^ j * (N.choose j : ℝ) := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun j _ => by rw [one_pow, mul_one]
  linarith

private theorem sum_choose_le (N k : ℕ) (hk : k ≤ N) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∑ j ∈ range (k + 1), (N.choose j : ℝ)) ≤ (1 + t) ^ N * (t ^ k)⁻¹ := by
  have hpos : (0 : ℝ) < t ^ k := by positivity
  have h := sum_choose_mul_le N k hk ht0 ht1
  have key : (∑ j ∈ range (k + 1), (N.choose j : ℝ)) * t ^ k ≤ (1 + t) ^ N := by linarith
  calc (∑ j ∈ range (k + 1), (N.choose j : ℝ))
      = (∑ j ∈ range (k + 1), (N.choose j : ℝ)) * t ^ k * (t ^ k)⁻¹ := by
        field_simp
    _ ≤ (1 + t) ^ N * (t ^ k)⁻¹ := mul_le_mul_of_nonneg_right key (by positivity)

private theorem exp_neg16_le : Real.exp (-16) ≤ 1 / 2000 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (2000 : ℝ) ≤ Real.exp 16 := by
    have he : Real.exp 16 = Real.exp 1 ^ (16 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (2000 : ℝ) ≤ 2 ^ (16 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (16 : ℕ) := by gcongr
  rw [Real.exp_neg, one_div]
  gcongr

/-- `Σ_{j ≤ k} C(N, j) ≤ exp(N/2000) · exp(16 k)` (take `t = e^{-16} ≤ 1/2000` above). -/
private theorem sum_choose_exp_bound (N k : ℕ) (hk : k ≤ N) :
    (∑ j ∈ range (k + 1), (N.choose j : ℝ))
      ≤ Real.exp ((N : ℝ) / 2000) * Real.exp (16 * (k : ℝ)) := by
  have ht0 : (0 : ℝ) < Real.exp (-16) := Real.exp_pos _
  have ht1 : Real.exp (-16) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hS := sum_choose_le N k hk ht0 ht1
  have htk : (Real.exp (-16) ^ k)⁻¹ = Real.exp (16 * (k : ℝ)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  have hOne : (1 + Real.exp (-16)) ^ N ≤ Real.exp ((N : ℝ) / 2000) := by
    have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    calc (1 + Real.exp (-16)) ^ N ≤ Real.exp (Real.exp (-16)) ^ N := by
          gcongr
          linarith [Real.add_one_le_exp (Real.exp (-16))]
      _ = Real.exp ((N : ℝ) * Real.exp (-16)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((N : ℝ) / 2000) := Real.exp_le_exp.2 (by nlinarith [exp_neg16_le])
  rw [htk] at hS
  exact hS.trans (mul_le_mul_of_nonneg_right hOne (by positivity))

private theorem eventually_four_mul_le_exp :
    ∀ᶠ y : ℝ in atTop, 4 * y ≤ Real.exp (y / 2000) := by
  filter_upwards [eventually_log_le (1 / 4000) (by norm_num), eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (4000 * Real.log 4)] with y hy hy0 hy4
  have h1 : Real.log (4 * y) = Real.log 4 + Real.log y :=
    Real.log_mul (by norm_num) (ne_of_gt hy0)
  have h2 : Real.log (4 * y) ≤ y / 2000 := by rw [h1]; linarith
  calc 4 * y = Real.exp (Real.log (4 * y)) := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp (y / 2000) := Real.exp_le_exp.2 h2

private theorem eventually_exp_neg_small :
    ∀ᶠ x : ℝ in atTop, Real.exp (-(x ^ ((1 : ℝ) / 12))) ≤ 1 / 2000 := by
  filter_upwards [(tendsto_rpow_atTop (y := (1 : ℝ) / 12)
    (by norm_num)).eventually_ge_atTop (Real.log 2000)] with x hx
  calc Real.exp (-(x ^ ((1 : ℝ) / 12))) ≤ Real.exp (-Real.log 2000) :=
        Real.exp_le_exp.2 (by linarith)
    _ = 1 / 2000 := by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]

/-- **`Lem_ParamChoice`, second half.**  For all large `N` and every `p ∈ [2N, 4N]`,
`p · 2^M · Σ_{j ≤ εp} C(N, j) ≤ 2^{N/240}`, i.e. Green's family `F` has at most
`2^{N/240}` members. -/
theorem eventually_family_bound :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 2 * N ≤ p → p ≤ 4 * N →
      (p : ℝ) * 2 ^ (MN N) * (∑ j ∈ range (⌊epsN N * (p : ℝ)⌋₊ + 1), (N.choose j : ℝ))
        ≤ 2 ^ ((N : ℝ) / 240) := by
  filter_upwards [eventually_ge_atTop 3,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually eventually_four_mul_le_exp,
    tendsto_log_nat.eventually eventually_exp_neg_small,
    epsN_tendsto_zero.eventually_le_const (show (0 : ℝ) < 1 / 128000 by norm_num)]
    with N hN3 hA hB hC
  intro p hp1 hp2
  have hN2 : 2 ≤ N := by omega
  have hNR0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpR : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hp2
  have hεnn : (0 : ℝ) ≤ epsN N := (epsN_pos hN2).le
  set k := ⌊epsN N * (p : ℝ)⌋₊ with hkdef
  have hkR : (k : ℝ) ≤ epsN N * (p : ℝ) := Nat.floor_le (by positivity)
  have hk16 : 16 * (k : ℝ) ≤ (N : ℝ) / 2000 := by
    have h1 : epsN N * (p : ℝ) ≤ 1 / 128000 * (4 * (N : ℝ)) :=
      mul_le_mul hC hpR (by positivity) (by norm_num)
    linarith
  have hkN : k ≤ N := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have : (k : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
  -- the three factors
  have hf1 : (p : ℝ) ≤ Real.exp ((N : ℝ) / 2000) := hpR.trans hA
  have hMle : (MN N : ℝ) ≤ (N : ℝ) / 2000 := by
    have h1 : (MN N : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) := by
      rw [MN]; exact Nat.floor_le (by positivity)
    have h2 : (N : ℝ) * Real.exp (-(Real.log N ^ ((1 : ℝ) / 12))) ≤ (N : ℝ) * (1 / 2000) :=
      mul_le_mul_of_nonneg_left hB hNR0
    linarith
  have hf2 : (2 : ℝ) ^ (MN N) ≤ Real.exp ((N : ℝ) / 2000) := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) ^ (MN N) ≤ Real.exp 1 ^ (MN N) := by gcongr
      _ = Real.exp ((MN N : ℝ)) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp ((N : ℝ) / 2000) := Real.exp_le_exp.2 hMle
  have hf3 : (∑ j ∈ range (k + 1), (N.choose j : ℝ))
      ≤ Real.exp ((N : ℝ) / 2000) * Real.exp ((N : ℝ) / 2000) :=
    (sum_choose_exp_bound N k hkN).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hk16) (by positivity))
  have hfinal : (p : ℝ) * 2 ^ (MN N) * (∑ j ∈ range (k + 1), (N.choose j : ℝ))
      ≤ Real.exp ((N : ℝ) / 2000) * Real.exp ((N : ℝ) / 2000) *
        (Real.exp ((N : ℝ) / 2000) * Real.exp ((N : ℝ) / 2000)) := by
    refine mul_le_mul (mul_le_mul hf1 hf2 (by positivity) (by positivity)) hf3 ?_ (by positivity)
    positivity
  have hcomb : Real.exp ((N : ℝ) / 2000) * Real.exp ((N : ℝ) / 2000) *
      (Real.exp ((N : ℝ) / 2000) * Real.exp ((N : ℝ) / 2000)) = Real.exp ((N : ℝ) / 500) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hlast : Real.exp ((N : ℝ) / 500) ≤ (2 : ℝ) ^ ((N : ℝ) / 240) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine Real.exp_le_exp.2 ?_
    have h2 : (0.48 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  linarith

end

/-! ## Axiom audit -/

#print axioms log_natCast_pos
#print axioms epsN_pos
#print axioms epsN_tendsto_zero
#print axioms MN_le
#print axioms LN_ge_one
#print axioms E_eq
#print axioms eventually_rpow_le_half
#print axioms log_le_two_rpow
#print axioms eventually_log_le
#print axioms eventually_log_params
#print axioms tendsto_log_nat
#print axioms two_le_MN_arg
#print axioms MN_lower
#print axioms eventually_MN_pos
#print axioms eventually_prop5_hypothesis
#print axioms sum_choose_mul_le
#print axioms sum_choose_le
#print axioms exp_neg16_le
#print axioms sum_choose_exp_bound
#print axioms eventually_four_mul_le_exp
#print axioms eventually_exp_neg_small
#print axioms eventually_family_bound

end CameronErdos
