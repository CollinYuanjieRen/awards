import Mathlib
import CameronErdos.Part1.SmallBinomial

/-!
# `Lem_Cor13_Numerics` — the real-exponent bookkeeping for Corollary 13

Green, *The Cameron–Erdős conjecture* (arXiv math/0304058), Corollary 13.
The proof of Corollary 13 splits the exceptional sum-free sets into four classes, each of which
is counted by a product of the shape `2^{θN} · (polynomial) · 3^{N/8} · 2^{…}`.  This file does
the arithmetic once and for all: every class is eventually bounded by `2^{0.498 N}`, and four
such bounds still fit under `2^{N/2}`.

The parameter used throughout is

`ρ_N = (64 ε_N)^{1/8} = 64^{1/8} (log N)^{-1/88}`,

written as a triple square root `√√√(64 ε_N)` to match `CameronErdos.Part1.SmallBinomial`.
-/

namespace CameronErdos

open Filter Topology

/-! ## Elementary helpers -/

/-- Monotonicity of `x ↦ 2^x` (real exponents). -/
private theorem two_rpow_le_two_rpow {x y : ℝ} (h : x ≤ y) : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

private theorem two_rpow_pos (x : ℝ) : (0 : ℝ) < (2 : ℝ) ^ x :=
  Real.rpow_pos_of_pos (by norm_num) x

/-- Truncated natural subtraction only ever decreases: an upper bound for `(a : ℝ) - b`
which is itself nonnegative is an upper bound for `((a - b : ℕ) : ℝ)`. -/
private theorem cast_nat_sub_le {a b : ℕ} {x : ℝ} (h : (a : ℝ) - b ≤ x) (hx : 0 ≤ x) :
    ((a - b : ℕ) : ℝ) ≤ x := by
  rcases le_or_gt b a with hba | hba
  · rw [Nat.cast_sub hba]; exact h
  · rw [Nat.sub_eq_zero_of_le hba.le]; simpa using hx

/-- Truncated natural subtraction dominates real subtraction. -/
private theorem le_cast_nat_sub (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_or_gt b a with hba | hba
  · rw [Nat.cast_sub hba]
  · have : (a : ℝ) ≤ b := by exact_mod_cast hba.le
    rw [Nat.sub_eq_zero_of_le hba.le]
    simp only [Nat.cast_zero]
    linarith

/-- `N / k ≥ N/k − 1` after casting. -/
private theorem cast_nat_div_ge (N k : ℕ) (hk : 0 < k) : (N : ℝ) / k - 1 ≤ ((N / k : ℕ) : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (k : ℝ) * ((N / k : ℕ) : ℝ) + ((N % k : ℕ) : ℝ) = N := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Nat.div_add_mod N k)
  have h2 : ((N % k : ℕ) : ℝ) < k := by exact_mod_cast Nat.mod_lt _ hk
  rw [sub_le_iff_le_add, div_le_iff₀ hk']
  nlinarith

/-- `3 ≤ 2^{127/80}`, i.e. `log₂ 3 ≤ 1.5875`; equivalently `3^80 ≤ 2^127`. -/
theorem three_le_two_rpow : (3 : ℝ) ≤ (2 : ℝ) ^ ((127 : ℝ) / 80) := by
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((127 : ℝ) / 80) := (two_rpow_pos _).le
  have hpow : ((2 : ℝ) ^ ((127 : ℝ) / 80)) ^ (80 : ℕ) = (2 : ℝ) ^ (127 : ℕ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((127 : ℝ) / 80)) 80, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 80) (by norm_num) h2 ?_
  rw [hpow]
  norm_num

/-- `3^q ≤ 2^{(127/80) q}` for natural `q`. -/
theorem three_pow_le_two_rpow (q : ℕ) : (3 : ℝ) ^ q ≤ (2 : ℝ) ^ (((127 : ℝ) / 80) * q) := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  exact pow_le_pow_left₀ (by norm_num) three_le_two_rpow q

/-- `x^2/4 ≤ exp x` for `x ≥ 0`. -/
private theorem sq_div_four_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 / 4 ≤ Real.exp x := by
  have h1 : x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
  have h2 : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [Real.exp_pos (x / 2)]

/-- `N ≤ 2^{bN}` eventually, for any `b > 0`. -/
theorem eventually_nat_le_two_rpow {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ≤ (2 : ℝ) ^ (b * N) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log 2 * b with hc
  have hcpos : 0 < c := by positivity
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually_ge_atTop (4 / c ^ 2), hcast.eventually_ge_atTop 0]
    with N hN hN0
  have hquad : (N : ℝ) ≤ (c * N) ^ 2 / 4 := by
    rw [div_le_iff₀ (by positivity)] at hN
    nlinarith
  have hexp : (c * N) ^ 2 / 4 ≤ Real.exp (c * N) := sq_div_four_le_exp (by positivity)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hce : Real.log 2 * (b * N) = c * N := by rw [hc]; ring
  rw [hce]
  linarith

/-! ## The parameter `ρ_N` -/

/-- `ρ_N = (64 ε_N)^{1/8}`, as a triple square root. -/
noncomputable def rho (N : ℕ) : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (64 * epsN N)))

theorem epsN_nonneg (N : ℕ) : 0 ≤ epsN N := by
  refine Real.rpow_nonneg ?_ _
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

theorem rho_nonneg (N : ℕ) : 0 ≤ rho N := Real.sqrt_nonneg _

theorem rho_eq (N : ℕ) :
    rho N = 64 ^ ((1 : ℝ) / 8) * Real.sqrt (Real.sqrt (Real.sqrt (epsN N))) := by
  have h64 : Real.sqrt (Real.sqrt (Real.sqrt 64)) = (64 : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 64), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 64)]
    norm_num
  rw [rho, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64), Real.sqrt_mul (Real.sqrt_nonneg _),
    Real.sqrt_mul (Real.sqrt_nonneg _), h64]

theorem rho_tendsto_zero : Tendsto rho atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => 64 * epsN N) atTop (𝓝 0) := by
    simpa using epsN_tendsto_zero.const_mul (64 : ℝ)
  have h3 := h.sqrt.sqrt.sqrt
  simp only [Real.sqrt_zero] at h3
  have hfun : rho = fun N : ℕ => Real.sqrt (Real.sqrt (Real.sqrt (64 * epsN N))) := rfl
  rw [hfun]
  exact h3

/-! ## `ρ_N` is small, but `ρ_N · N` is large -/

theorem eventually_rho_pos : ∀ᶠ N : ℕ in atTop, 0 < rho N := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have h := epsN_pos hN
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by linarith)))

/-- `ρ_N N → ∞`: indeed `ρ_N ≥ (log N)^{-1}` and `N = exp (log N) ≥ (log N)^2/4`. -/
theorem eventually_rho_mul_nat : ∀ᶠ N : ℕ in atTop, (1000 : ℝ) ≤ rho N * N := by
  filter_upwards [tendsto_log_nat.eventually_ge_atTop 4000, eventually_ge_atTop 3] with N hu hN3
  have hN3' : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set u : ℝ := Real.log (N : ℝ) with hudef
  have hu1 : (1 : ℝ) ≤ u := by simp only [hudef] at hu ⊢; linarith
  have hupos : (0 : ℝ) < u := by linarith
  have heps : 1 / u ≤ epsN N := by
    have h1 : u ^ ((1 : ℝ) / 11) ≤ u ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    rw [Real.rpow_one] at h1
    have h2 : (0 : ℝ) < u ^ ((1 : ℝ) / 11) := Real.rpow_pos_of_pos hupos _
    have h3 : epsN N = (u ^ ((1 : ℝ) / 11))⁻¹ := by
      rw [epsN, ← Real.rpow_neg hupos.le]
    rw [h3, one_div, ← one_div, ← one_div]
    exact one_div_le_one_div_of_le h2 h1
  have hinv : 0 < 1 / u := by positivity
  have hle1 : 1 / u ≤ 1 := by
    rw [div_le_one hupos]; linarith
  have h8 : (1 / u) ^ (8 : ℕ) ≤ 1 / u := by
    have := pow_le_pow_of_le_one hinv.le hle1 (by norm_num : (1 : ℕ) ≤ 8)
    simpa using this
  have hεnn : (0 : ℝ) ≤ epsN N := epsN_nonneg N
  have hrho : 1 / u ≤ rho N := by
    simp only [rho]
    refine Real.le_sqrt_of_sq_le (Real.le_sqrt_of_sq_le (Real.le_sqrt_of_sq_le ?_))
    have hexp : (((1 / u) ^ 2) ^ 2) ^ 2 = (1 / u) ^ (8 : ℕ) := by ring
    rw [hexp]
    linarith
  have hexpu : Real.exp u = (N : ℝ) := Real.exp_log hNpos
  have hNlb : u ^ 2 / 4 ≤ (N : ℝ) := by
    rw [← hexpu]; exact sq_div_four_le_exp hupos.le
  have hu4000 : (4000 : ℝ) ≤ u := by simp only [hudef] at hu ⊢; linarith
  calc (1000 : ℝ) ≤ u / 4 := by linarith
    _ = (1 / u) * (u ^ 2 / 4) := by field_simp
    _ ≤ rho N * N := mul_le_mul hrho hNlb (by positivity) (rho_nonneg N)

/-- **`Lem_Cor13_Numerics`, the `ρ` package.** -/
theorem eventually_rho_small : ∀ᶠ N : ℕ in atTop,
    0 < rho N ∧ rho N ≤ 1 / 10 ^ 4 ∧ (1000 : ℝ) ≤ rho N * N ∧ 64 * epsN N ≤ 1 / 10 ^ 32 := by
  have h2 : ∀ᶠ N : ℕ in atTop, rho N ≤ 1 / 10 ^ 4 :=
    rho_tendsto_zero.eventually_le_const (by norm_num)
  have h4 : ∀ᶠ N : ℕ in atTop, 64 * epsN N ≤ 1 / 10 ^ 32 := by
    have h : Tendsto (fun N : ℕ => 64 * epsN N) atTop (𝓝 0) := by
      simpa using epsN_tendsto_zero.const_mul (64 : ℝ)
    exact h.eventually_le_const (by norm_num)
  filter_upwards [eventually_rho_pos, h2, eventually_rho_mul_nat, h4] with N ha hb hc hd
  exact ⟨ha, hb, hc, hd⟩

/-! ## The four exponent estimates, and the final `2^{N/2}` bound -/

/-- **(N1)** `2^{N/1000} · 2^{(1/2 − 1/120)N} ≤ 2^{0.498 N}` (exponent `0.49267`). -/
theorem numerics_N1 : ∀ᶠ N : ℕ in atTop,
    (2 : ℝ) ^ ((N : ℝ) / 1000) * 2 ^ ((1 / 2 - 1 / 120 : ℝ) * N) ≤ 2 ^ ((0.498 : ℝ) * N) := by
  refine Eventually.of_forall fun N => ?_
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine two_rpow_le_two_rpow ?_
  have hn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

/-- **(N2)** the even-case count. -/
theorem numerics_N2 : ∀ᶠ N : ℕ in atTop,
    (2 : ℝ) ^ ((N : ℝ) / 1000) * ((N / 2 : ℕ) : ℝ) * (3 : ℝ) ^ (N / 8) *
      (2 : ℝ) ^ ((N + 1) / 2 - 2 * (N / 8)) ≤ 2 ^ ((0.498 : ℝ) * N) := by
  filter_upwards [eventually_nat_le_two_rpow (b := (1 : ℝ) / 1000) (by norm_num),
    eventually_ge_atTop 100] with N hbig hN100
  have hn : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN100
  have hA : ((N / 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((1 : ℝ) / 1000) * N) :=
    le_trans (by exact_mod_cast Nat.div_le_self N 2) hbig
  have hq : ((N / 8 : ℕ) : ℝ) ≤ (N : ℝ) / 8 := Nat.cast_div_le
  have hB : (3 : ℝ) ^ (N / 8) ≤ (2 : ℝ) ^ (((127 : ℝ) / 80) * ((N : ℝ) / 8)) :=
    le_trans (three_pow_le_two_rpow _) (two_rpow_le_two_rpow (by linarith))
  have hm : (((N + 1) / 2 - 2 * (N / 8) : ℕ) : ℝ) ≤ (N : ℝ) / 4 + 5 / 2 := by
    refine cast_nat_sub_le ?_ (by positivity)
    have h1 : (((N + 1) / 2 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
      have h := Nat.cast_div_le (α := ℝ) (m := N + 1) (n := 2)
      push_cast at h
      linarith
    have h2 : (N : ℝ) / 8 - 1 ≤ ((N / 8 : ℕ) : ℝ) := cast_nat_div_ge N 8 (by norm_num)
    push_cast
    linarith
  have hC : (2 : ℝ) ^ ((N + 1) / 2 - 2 * (N / 8)) ≤ (2 : ℝ) ^ ((N : ℝ) / 4 + 5 / 2) := by
    rw [← Real.rpow_natCast (2 : ℝ) ((N + 1) / 2 - 2 * (N / 8))]
    exact two_rpow_le_two_rpow hm
  have hfin : (2 : ℝ) ^ ((N : ℝ) / 1000) * (2 : ℝ) ^ (((1 : ℝ) / 1000) * N) *
      (2 : ℝ) ^ (((127 : ℝ) / 80) * ((N : ℝ) / 8)) * (2 : ℝ) ^ ((N : ℝ) / 4 + 5 / 2)
      ≤ 2 ^ ((0.498 : ℝ) * N) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact two_rpow_le_two_rpow (by nlinarith)
  refine le_trans ?_ hfin
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hA (two_rpow_pos _).le) hB
    (by positivity) (by positivity)) hC (by positivity) (by positivity)

/-- **(N3)** the shorter-interval count. -/
theorem numerics_N3 : ∀ᶠ N : ℕ in atTop,
    (2 : ℝ) ^ ((1 / 2 + 1 / 1000 : ℝ) * ((N - N / 120 : ℕ) : ℝ)) * 2 ^ ((N : ℝ) / 1000)
      ≤ 2 ^ ((0.498 : ℝ) * N) := by
  filter_upwards [eventually_ge_atTop 3000] with N hN
  have hn : (3000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsub : ((N - N / 120 : ℕ) : ℝ) ≤ (119 / 120) * N + 1 := by
    refine cast_nat_sub_le ?_ (by positivity)
    have h2 : (N : ℝ) / 120 - 1 ≤ ((N / 120 : ℕ) : ℝ) := cast_nat_div_ge N 120 (by norm_num)
    linarith
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine two_rpow_le_two_rpow ?_
  linarith

/-- **(N4)** the interval count with a small element. -/
theorem numerics_N4 : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * (2 : ℝ) ^ ((N : ℝ) / 1000) * (3 : ℝ) ^ (N / 8 - 4) *
      (2 : ℝ) ^ ((N + 1 - ⌈(1 / 2 - 1 / 30 - 60 * rho N) * N⌉₊) - 2 * (N / 8 - 4))
      ≤ 2 ^ ((0.498 : ℝ) * N) := by
  filter_upwards [eventually_nat_le_two_rpow (b := (1 : ℝ) / 1000) (by norm_num),
    eventually_rho_small, eventually_ge_atTop 1500] with N hbig hrho hN1500
  obtain ⟨hρpos, hρsmall, -, -⟩ := hrho
  have hn : (1500 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1500
  have hn0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  set ρ : ℝ := rho N with hρdef
  set q : ℕ := N / 8 - 4 with hqdef
  set w : ℕ := ⌈(1 / 2 - 1 / 30 - 60 * ρ) * N⌉₊ with hwdef
  have hqle : (q : ℝ) ≤ (N : ℝ) / 8 := by
    refine le_trans ?_ (Nat.cast_div_le (α := ℝ) (m := N) (n := 8))
    exact_mod_cast Nat.sub_le (N / 8) 4
  have hqge : (N : ℝ) / 8 - 5 ≤ (q : ℝ) := by
    have h1 : ((N / 8 : ℕ) : ℝ) - 4 ≤ (q : ℝ) := by
      have h := le_cast_nat_sub (N / 8) 4
      push_cast at h
      linarith
    have h2 := cast_nat_div_ge N 8 (by norm_num)
    linarith
  have hw : (1 / 2 - 1 / 30 - 60 * ρ) * N ≤ (w : ℝ) := Nat.le_ceil _
  have hρn : 60 * ρ * (N : ℝ) ≤ (6 / 1000) * (N : ℝ) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 10 ^ 4 - ρ) hn0]
  have hm : (((N + 1 - w) - 2 * q : ℕ) : ℝ) ≤ (1 / 4 + 1 / 30 + 60 * ρ) * N + 11 := by
    have hnn : (0 : ℝ) ≤ (1 / 4 + 1 / 30 + 60 * ρ) * N + 11 := by nlinarith
    refine cast_nat_sub_le ?_ hnn
    have hsub1 : ((N + 1 - w : ℕ) : ℝ) ≤ (1 / 2 + 1 / 30 + 60 * ρ) * N + 1 := by
      refine cast_nat_sub_le ?_ (by nlinarith)
      push_cast
      linarith
    push_cast
    linarith
  have hB : (3 : ℝ) ^ q ≤ (2 : ℝ) ^ (((127 : ℝ) / 80) * ((N : ℝ) / 8)) :=
    le_trans (three_pow_le_two_rpow q) (two_rpow_le_two_rpow (by linarith))
  have hC : (2 : ℝ) ^ ((N + 1 - w) - 2 * q) ≤ (2 : ℝ) ^ ((1 / 4 + 1 / 30 + 60 * ρ) * N + 11) := by
    rw [← Real.rpow_natCast (2 : ℝ) ((N + 1 - w) - 2 * q)]
    exact two_rpow_le_two_rpow hm
  have hfin : (2 : ℝ) ^ (((1 : ℝ) / 1000) * N) * (2 : ℝ) ^ ((N : ℝ) / 1000) *
      (2 : ℝ) ^ (((127 : ℝ) / 80) * ((N : ℝ) / 8)) *
      (2 : ℝ) ^ ((1 / 4 + 1 / 30 + 60 * ρ) * N + 11) ≤ 2 ^ ((0.498 : ℝ) * N) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    refine two_rpow_le_two_rpow ?_
    nlinarith
  refine le_trans ?_ hfin
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hbig (two_rpow_pos _).le) hB
    (by positivity) (by positivity)) hC (by positivity) (by positivity)

/-- **(N5)** four classes of size `2^{0.498N}` still fit under `2^{N/2}`. -/
theorem numerics_N5 : ∀ᶠ N : ℕ in atTop,
    4 * (2 : ℝ) ^ ((0.498 : ℝ) * N) ≤ 2 ^ ((N : ℝ) / 2) := by
  filter_upwards [eventually_ge_atTop 1000] with N hN
  have hn : (1000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h4, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine two_rpow_le_two_rpow ?_
  linarith

/-! ## Small binomial sums in `ρ`-form -/

/-- `Lem_SmallBinomial` rewritten with `ρ_N` in place of `ε_N^{1/8}`. -/
theorem eventually_small_binomial_rho (c θ : ℝ) (hc : 0 < c) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ c * rho N * N →
      ∑ j ∈ Finset.range (k + 1), (N.choose j : ℝ) ≤ (2 : ℝ) ^ (θ * N) := by
  have h64 : (0 : ℝ) < (64 : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos (by norm_num) _
  filter_upwards [eventually_small_binomial (c * 64 ^ ((1 : ℝ) / 8)) θ (by positivity) hθ]
    with N hN k hk
  refine hN k ?_
  rw [rho_eq] at hk
  calc (k : ℝ) ≤ c * (64 ^ ((1 : ℝ) / 8) * Real.sqrt (Real.sqrt (Real.sqrt (epsN N)))) * N := hk
    _ = c * 64 ^ ((1 : ℝ) / 8) * Real.sqrt (Real.sqrt (Real.sqrt (epsN N))) * N := by ring

/-- Binomial coefficients are monotone in the top argument: the `N/2`-sum is at most the
`N`-sum. -/
theorem sum_choose_half_le (N k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), ((N / 2).choose j : ℝ)
      ≤ ∑ j ∈ Finset.range (k + 1), (N.choose j : ℝ) := by
  refine Finset.sum_le_sum fun j _ => ?_
  exact_mod_cast Nat.choose_le_choose j (Nat.div_le_self N 2)

end CameronErdos

#print axioms CameronErdos.two_rpow_le_two_rpow
#print axioms CameronErdos.two_rpow_pos
#print axioms CameronErdos.cast_nat_sub_le
#print axioms CameronErdos.le_cast_nat_sub
#print axioms CameronErdos.cast_nat_div_ge
#print axioms CameronErdos.sq_div_four_le_exp
#print axioms CameronErdos.three_le_two_rpow
#print axioms CameronErdos.three_pow_le_two_rpow
#print axioms CameronErdos.eventually_nat_le_two_rpow
#print axioms CameronErdos.epsN_nonneg
#print axioms CameronErdos.rho_nonneg
#print axioms CameronErdos.rho_eq
#print axioms CameronErdos.rho_tendsto_zero
#print axioms CameronErdos.eventually_rho_pos
#print axioms CameronErdos.eventually_rho_mul_nat
#print axioms CameronErdos.eventually_rho_small
#print axioms CameronErdos.numerics_N1
#print axioms CameronErdos.numerics_N2
#print axioms CameronErdos.numerics_N3
#print axioms CameronErdos.numerics_N4
#print axioms CameronErdos.numerics_N5
#print axioms CameronErdos.eventually_small_binomial_rho
#print axioms CameronErdos.sum_choose_half_le
