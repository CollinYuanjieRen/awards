import Mathlib

/-!
# JSP-001010 / Erdős #1205 — asymptotic bookkeeping

This file collects the purely analytic facts used in the assembly of the lower bound
(`eventually_facts`), together with the two soft consequences of the two-sided bounds
on `F`: `F x / log x → 1` and `F x - log x = O(√(log x · log log x))`.
-/

open Filter Topology Real

namespace Erdos1205

/-! ### Auxiliary limits -/

/-- A crude but sufficient growth bound: `2 log L ≤ L - 1` for `L ≥ 100`. -/
private lemma two_log_le_sub_one {L : ℝ} (h : 100 ≤ L) : 2 * Real.log L ≤ L - 1 := by
  have hLpos : (0:ℝ) < L := by linarith
  have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
  have hs10 : 10 ≤ Real.sqrt L := by
    have h1 : Real.sqrt 100 ≤ Real.sqrt L := Real.sqrt_le_sqrt h
    rwa [show (100:ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h1
  have hlogs : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  rw [Real.log_sqrt hLpos.le] at hlogs
  nlinarith [hs, hs10]

/-- `√(u log u)/u → 0` as `u → ∞`. -/
private lemma tendsto_sqrt_mul_log_div_self :
    Tendsto (fun u : ℝ => Real.sqrt (u * Real.log u) / u) atTop (𝓝 0) := by
  have h0 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h1 : Tendsto (fun u : ℝ => Real.sqrt (Real.log u / u)) atTop (𝓝 0) := by
    simpa using h0.sqrt
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (1:ℝ)] with u hu hu1
  have hlog : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
  have h2 : Real.sqrt (Real.log u / u) * u = Real.sqrt (u * Real.log u) := by
    have h3 : Real.sqrt (Real.log u / u) * u
        = Real.sqrt (Real.log u / u) * Real.sqrt (u ^ 2) := by
      rw [Real.sqrt_sq hu.le]
    rw [h3, ← Real.sqrt_mul (div_nonneg hlog hu.le)]
    congr 1
    field_simp
  rw [eq_div_iff hu.ne']
  exact h2

/-- `(u + 2)/u → 1`. -/
private lemma tendsto_add_two_div_self :
    Tendsto (fun u : ℝ => (u + 2) / u) atTop (𝓝 1) := by
  have h : Tendsto (fun u : ℝ => 1 + 2 / u) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  field_simp

/-- `(u - C√(u log u))/u → 1`. -/
private lemma tendsto_sub_sqrt_div_self (C : ℝ) :
    Tendsto (fun u : ℝ => (u - C * Real.sqrt (u * Real.log u)) / u) atTop (𝓝 1) := by
  have h : Tendsto (fun u : ℝ => 1 - C * (Real.sqrt (u * Real.log u) / u)) atTop
      (𝓝 (1 - C * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_sqrt_mul_log_div_self)
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  field_simp

/-- `log x → ∞` along the naturals. -/
private lemma tendsto_log_nat : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `log log x → ∞` along the naturals. -/
private lemma tendsto_loglog_nat :
    Tendsto (fun x : ℕ => Real.log (Real.log x)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_nat

/-! ### The quantitative facts -/

/-- The quantitative facts used in the assembly, for all large `x`; `N = x/2`, `μ = harmonic N`,
`t = √(8 μ log log x)`. -/
theorem eventually_facts : ∀ᶠ x : ℕ in atTop, ∀ (N : ℕ) (μ t : ℝ),
    N = x / 2 → μ = (harmonic N : ℝ) → t = Real.sqrt (8 * μ * Real.log (Real.log x)) →
      (2 ≤ x) ∧ (1 ≤ N) ∧
      (Real.log x - 1 ≤ μ) ∧ (μ ≤ Real.log x + 1) ∧
      (0 ≤ t) ∧ (t ≤ 2 * μ) ∧
      (Real.exp (-(t ^ 2) / (4 * μ)) ≤ ((Real.log x) ^ 2)⁻¹) ∧
      ((x : ℝ) * ((Real.log x) ^ 2)⁻¹ * (μ + 1) ≤ ((x - N : ℕ) : ℝ)) ∧
      (Real.log x - 6 * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ μ - t - 1) := by
  filter_upwards [eventually_ge_atTop 2, tendsto_log_nat.eventually_ge_atTop 100,
    tendsto_loglog_nat.eventually_ge_atTop 100] with x hx2 hL hLL
  intro N μ t hN hμ ht
  set L : ℝ := Real.log x with hLdef
  set LL : ℝ := Real.log (Real.log x) with hLLdef
  -- basic positivity
  have hxpos : (0:ℝ) < (x : ℝ) := by
    have : (2:ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
    linarith
  have hLpos : (0:ℝ) < L := by linarith
  have hLLpos : (0:ℝ) < LL := by linarith
  have hN1 : 1 ≤ N := by omega
  have hNx : N ≤ x := by omega
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- `log x - 1 ≤ μ`
  have hμlow : L - 1 ≤ μ := by
    have hcast : (x : ℝ) / 2 ≤ (N : ℝ) + 1 := by
      have h1 : x ≤ 2 * N + 2 := by omega
      have h2 : ((x : ℕ) : ℝ) ≤ ((2 * N + 2 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    have h1 : Real.log ((x : ℝ) / 2) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (by positivity) hcast
    have h2 : Real.log ((N : ℝ) + 1) ≤ μ := by
      rw [hμ]
      have := log_add_one_le_harmonic N
      push_cast at this
      exact this
    have h3 : Real.log ((x : ℝ) / 2) = L - Real.log 2 :=
      Real.log_div (ne_of_gt hxpos) (by norm_num)
    have h4 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    linarith
  -- `μ ≤ log x + 1`
  have hμhigh : μ ≤ L + 1 := by
    have h5 : μ ≤ 1 + Real.log (N : ℝ) := by rw [hμ]; exact harmonic_le_one_add_log N
    have h6 : Real.log (N : ℝ) ≤ L := by
      refine Real.log_le_log hNpos ?_
      exact_mod_cast hNx
    linarith
  have hμpos : (0:ℝ) < μ := by linarith
  -- `2 log log x ≤ μ`
  have hLLμ : 2 * LL ≤ μ := by
    have := two_log_le_sub_one hL
    rw [← hLLdef] at this
    linarith
  -- basic facts about `t`
  have h8 : (0:ℝ) ≤ 8 * μ * LL := by positivity
  have htnn : 0 ≤ t := by rw [ht]; exact Real.sqrt_nonneg _
  have htsq : t ^ 2 = 8 * μ * LL := by rw [ht]; exact Real.sq_sqrt h8
  have ht2μ : t ≤ 2 * μ := by
    rw [ht]
    have hle : 8 * μ * LL ≤ (2 * μ) ^ 2 := by nlinarith
    calc Real.sqrt (8 * μ * LL) ≤ Real.sqrt ((2 * μ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 2 * μ := Real.sqrt_sq (by linarith)
  -- the exponential bound
  have hexp : Real.exp (-(t ^ 2) / (4 * μ)) ≤ (L ^ 2)⁻¹ := by
    refine le_of_eq ?_
    rw [htsq]
    have harg : -(8 * μ * LL) / (4 * μ) = -LL + -LL := by
      field_simp
      ring
    rw [harg, Real.exp_add, Real.exp_neg, Real.exp_log hLpos, sq, mul_inv]
  -- the size of the set of big moduli
  have hbig : (x : ℝ) * (L ^ 2)⁻¹ * (μ + 1) ≤ ((x - N : ℕ) : ℝ) := by
    have hsub : (x : ℝ) / 2 ≤ ((x - N : ℕ) : ℝ) := by
      have hcast : ((x - N : ℕ) : ℝ) = (x : ℝ) - (N : ℝ) := Nat.cast_sub hNx
      have h2N : 2 * N ≤ x := by omega
      have h2N' : (2:ℝ) * (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast h2N
      rw [hcast]; linarith
    have hL2 : (0:ℝ) < L ^ 2 := by positivity
    have key : (L ^ 2)⁻¹ * (μ + 1) ≤ 1 / 2 := by
      have hmono : (L ^ 2)⁻¹ * (μ + 1) ≤ (L ^ 2)⁻¹ * (L ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hL2))
        nlinarith
      calc (L ^ 2)⁻¹ * (μ + 1) ≤ (L ^ 2)⁻¹ * (L ^ 2 / 2) := hmono
        _ = 1 / 2 := by field_simp
    have := mul_le_mul_of_nonneg_left key hxpos.le
    calc (x : ℝ) * (L ^ 2)⁻¹ * (μ + 1) = (x : ℝ) * ((L ^ 2)⁻¹ * (μ + 1)) := by ring
      _ ≤ (x : ℝ) * (1 / 2) := this
      _ = (x : ℝ) / 2 := by ring
      _ ≤ ((x - N : ℕ) : ℝ) := hsub
  -- the final inequality
  have hfin : L - 6 * Real.sqrt (L * LL) ≤ μ - t - 1 := by
    have hLLnn : (0:ℝ) ≤ L * LL := by positivity
    have hsq : Real.sqrt (L * LL) ^ 2 = L * LL := Real.sq_sqrt hLLnn
    have hs1 : (1:ℝ) ≤ Real.sqrt (L * LL) := by
      have h1 : Real.sqrt 1 ≤ Real.sqrt (L * LL) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_one] at h1
    have ht4 : t ≤ 4 * Real.sqrt (L * LL) := by
      rw [ht]
      have hle : 8 * μ * LL ≤ (4 * Real.sqrt (L * LL)) ^ 2 := by
        have hexpand : (4 * Real.sqrt (L * LL)) ^ 2 = 16 * (L * LL) := by
          rw [mul_pow, hsq]; ring
        rw [hexpand]
        nlinarith
      calc Real.sqrt (8 * μ * LL) ≤ Real.sqrt ((4 * Real.sqrt (L * LL)) ^ 2) :=
            Real.sqrt_le_sqrt hle
        _ = 4 * Real.sqrt (L * LL) := Real.sqrt_sq (by positivity)
    linarith
  exact ⟨hx2, hN1, hμlow, hμhigh, htnn, ht2μ, hexp, hbig, hfin⟩

/-! ### Soft consequences of the two-sided bounds -/

/-- From the two-sided bounds, `f x / log x → 1`. -/
theorem tendsto_div_log_of_bounds (f : ℕ → ℝ) (C : ℝ)
    (h1 : ∀ᶠ x : ℕ in atTop, f x ≤ Real.log x + 2)
    (h2 : ∀ᶠ x : ℕ in atTop, Real.log x - C * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ f x) :
    Tendsto (fun x : ℕ => f x / Real.log x) atTop (𝓝 1) := by
  have hup : Tendsto (fun x : ℕ => (Real.log x + 2) / Real.log x) atTop (𝓝 1) :=
    tendsto_add_two_div_self.comp tendsto_log_nat
  have hlo : Tendsto (fun x : ℕ =>
      (Real.log x - C * Real.sqrt (Real.log x * Real.log (Real.log x))) / Real.log x)
      atTop (𝓝 1) :=
    (tendsto_sub_sqrt_div_self C).comp tendsto_log_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [h2, tendsto_log_nat.eventually_gt_atTop 0] with x hx hLx
    gcongr
  · filter_upwards [h1, tendsto_log_nat.eventually_gt_atTop 0] with x hx hLx
    gcongr

/-- From the two-sided bounds, `f x − log x = O(√(log x · log log x))`. -/
theorem isBigO_sub_log_of_bounds (f : ℕ → ℝ) (C : ℝ)
    (h1 : ∀ᶠ x : ℕ in atTop, f x ≤ Real.log x + 2)
    (h2 : ∀ᶠ x : ℕ in atTop, Real.log x - C * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ f x) :
    (fun x : ℕ => f x - Real.log x) =O[atTop] fun x : ℕ =>
      Real.sqrt (Real.log x * Real.log (Real.log x)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨|C| + 2, ?_⟩
  filter_upwards [h1, h2, tendsto_log_nat.eventually_ge_atTop 1,
    tendsto_loglog_nat.eventually_ge_atTop 1] with x hx1 hx2 hLx hLLx
  set s : ℝ := Real.sqrt (Real.log x * Real.log (Real.log x)) with hs
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : (1:ℝ) ≤ s := by
    have h : Real.sqrt 1 ≤ s := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_one] at h
  have hCs : C * s ≤ |C| * s := by
    have := le_abs_self C
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsnn, abs_le]
  have hCnn : (0:ℝ) ≤ |C| * s := mul_nonneg (abs_nonneg C) hsnn
  constructor
  · nlinarith
  · nlinarith

end Erdos1205

