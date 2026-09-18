import Mathlib

/-!
# JSP-000539 / Erdős #664 — the asymptotic estimates

This file is pure real analysis: it contains the two analytic ingredients used by the
probabilistic construction.

* `exists_M` : for every `c₀ < 1` there is a modulus `M ≥ 5` with `M ^ (1 - c₀) > 2`.
* `eventually_sum_lt_one` : for such an `M` the total failure probability
  `p² (2 M^{c₀-1})^p + p² (2 M^{-1/2})^p + (p²+1)^{2p(C+1)} (1 - M^{-(4C+3)})^{p²/2}`
  (written out with natural number floors and divisions, exactly as produced by the counting
  arguments) is `< 1` for all large `p`.

The three summands are handled separately by `term1_tendsto`, `term2_tendsto`, `term3_tendsto`,
each of which shows the corresponding expression tends to `0` along `atTop`.
-/

namespace Erdos664

open Filter Topology Real

/-! ### Choosing the modulus `M` -/

/-- For every `c₀ < 1` there is an integer `M ≥ 5` with `2 < M ^ (1 - c₀)` (real power). -/
theorem exists_M (c₀ : ℝ) (hc : c₀ < 1) : ∃ M : ℕ, 5 ≤ M ∧ (2 : ℝ) < (M : ℝ) ^ (1 - c₀) := by
  have hpos : 0 < 1 - c₀ := by linarith
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / (1 - c₀))
  set k : ℕ := max j 3 with hk
  refine ⟨2 ^ k, ?_, ?_⟩
  · calc (5 : ℕ) ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  · have hjk : (j : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.cast_le.2 (le_max_left j 3)
    have h1 : (1 : ℝ) < (k : ℝ) * (1 - c₀) := by
      have : (1 : ℝ) / (1 - c₀) < (k : ℝ) := lt_of_lt_of_le hj hjk
      rw [div_lt_iff₀ hpos] at this
      linarith
    have hcast : (((2 : ℕ) ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    rw [hcast, ← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ < (2 : ℝ) ^ ((k : ℝ) * (1 - c₀)) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1

/-! ### Elementary facts about the three ratios -/

/-- The geometric ratio of the first term is `< 1`. -/
theorem theta1_lt_one (c₀ : ℝ) (M : ℕ) (hM5 : 5 ≤ M) (hM : (2 : ℝ) < (M : ℝ) ^ (1 - c₀)) :
    2 * (M : ℝ) ^ (c₀ - 1) < 1 := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hx : (0 : ℝ) < (M : ℝ) ^ (1 - c₀) := lt_trans (by norm_num) hM
  have hneg : (M : ℝ) ^ (c₀ - 1) = ((M : ℝ) ^ (1 - c₀))⁻¹ := by
    rw [show c₀ - 1 = -(1 - c₀) by ring, Real.rpow_neg hM0.le]
  rw [hneg]
  have h := mul_lt_mul_of_pos_right hM (inv_pos.2 hx)
  rwa [mul_inv_cancel₀ hx.ne'] at h

/-- The geometric ratio of the second term is `< 1`. -/
theorem theta2_lt_one (M : ℕ) (hM5 : 5 ≤ M) : 2 / Real.sqrt (M : ℝ) < 1 := by
  have hM5' : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM5
  have hs : (2 : ℝ) < Real.sqrt (M : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  rw [div_lt_one (by linarith)]
  exact hs

/-- The parameter `η = M^{-(4C+3)}` is positive. -/
theorem eta_pos (M : ℕ) (hM5 : 5 ≤ M) (C : ℕ) : 0 < (1 / (M : ℝ)) ^ (4 * C + 3) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  positivity

/-- The parameter `η = M^{-(4C+3)}` is less than `1`. -/
theorem eta_lt_one (M : ℕ) (hM5 : 5 ≤ M) (C : ℕ) : (1 / (M : ℝ)) ^ (4 * C + 3) < 1 := by
  have hM5' : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM5
  have h1 : 1 / (M : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  exact pow_lt_one₀ (by positivity) h1 (by omega)

/-! ### The three limits -/

/-- First term: the probability that some line keeps at most `⌊c₀ p⌋` points. -/
theorem term1_tendsto (c₀ : ℝ) (h0 : 0 ≤ c₀) (_hc : c₀ < 1) (M : ℕ) (hM5 : 5 ≤ M)
    (hM : (2 : ℝ) < (M : ℝ) ^ (1 - c₀)) :
    Tendsto (fun p : ℕ => (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ (⌊c₀ * p⌋₊) / (M : ℝ) ^ p)
      atTop (𝓝 0) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
    have : 1 ≤ M := by omega
    exact_mod_cast this
  have key : ∀ p : ℕ, (M : ℝ) ^ (⌊c₀ * (p : ℝ)⌋₊) / (M : ℝ) ^ p
      ≤ ((M : ℝ) ^ (c₀ - 1)) ^ p := by
    intro p
    have h1 : (M : ℝ) ^ (⌊c₀ * (p : ℝ)⌋₊) ≤ (M : ℝ) ^ (c₀ * (p : ℝ)) := by
      rw [← Real.rpow_natCast (M : ℝ) (⌊c₀ * (p : ℝ)⌋₊)]
      exact Real.rpow_le_rpow_of_exponent_le hM1
        (Nat.floor_le (mul_nonneg h0 (Nat.cast_nonneg p)))
    have h2 : ((M : ℝ) ^ (c₀ - 1)) ^ p = (M : ℝ) ^ (c₀ * (p : ℝ)) / (M : ℝ) ^ p := by
      rw [← Real.rpow_natCast ((M : ℝ) ^ (c₀ - 1)) p, ← Real.rpow_mul hM0.le,
        ← Real.rpow_natCast (M : ℝ) p, ← Real.rpow_sub hM0]
      congr 1
      ring
    rw [h2]
    gcongr
  refine squeeze_zero (fun p => by positivity) (fun p => ?_)
    (tendsto_pow_const_mul_const_pow_of_lt_one 2 (by positivity)
      (theta1_lt_one c₀ M hM5 hM))
  calc (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ (⌊c₀ * (p : ℝ)⌋₊) / (M : ℝ) ^ p
      = (p : ℝ) ^ 2 * 2 ^ p * ((M : ℝ) ^ (⌊c₀ * (p : ℝ)⌋₊) / (M : ℝ) ^ p) := by
        ring
    _ ≤ (p : ℝ) ^ 2 * 2 ^ p * ((M : ℝ) ^ (c₀ - 1)) ^ p := by
        have := key p
        gcongr
    _ = (p : ℝ) ^ 2 * (2 * (M : ℝ) ^ (c₀ - 1)) ^ p := by
        rw [mul_pow]; ring

/-- Second term: the probability that some point has small degree. -/
theorem term2_tendsto (M : ℕ) (hM5 : 5 ≤ M) :
    Tendsto (fun p : ℕ => (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ (p / 2) / (M : ℝ) ^ p)
      atTop (𝓝 0) := by
  have hM5' : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM5
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hs2 : (2 : ℝ) < Real.sqrt (M : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have hs0 : (0 : ℝ) < Real.sqrt (M : ℝ) := by linarith
  have hsq : Real.sqrt (M : ℝ) ^ 2 = (M : ℝ) := Real.sq_sqrt hM0.le
  have key : ∀ p : ℕ, (M : ℝ) ^ (p / 2) / (M : ℝ) ^ p
      ≤ (1 / Real.sqrt (M : ℝ)) ^ p := by
    intro p
    have h1 : (M : ℝ) ^ (p / 2) ≤ Real.sqrt (M : ℝ) ^ p := by
      have he : (M : ℝ) ^ (p / 2) = Real.sqrt (M : ℝ) ^ (2 * (p / 2)) := by
        rw [pow_mul, hsq]
      rw [he]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    have h2 : (1 / Real.sqrt (M : ℝ)) ^ p = Real.sqrt (M : ℝ) ^ p / (M : ℝ) ^ p := by
      rw [← Real.sqrt_div_self', div_pow]
    rw [h2]
    gcongr
  refine squeeze_zero (fun p => by positivity) (fun p => ?_)
    (tendsto_pow_const_mul_const_pow_of_lt_one 2 (by positivity) (theta2_lt_one M hM5))
  calc (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ (p / 2) / (M : ℝ) ^ p
      = (p : ℝ) ^ 2 * 2 ^ p * ((M : ℝ) ^ (p / 2) / (M : ℝ) ^ p) := by ring
    _ ≤ (p : ℝ) ^ 2 * 2 ^ p * (1 / Real.sqrt (M : ℝ)) ^ p := by
        have := key p
        gcongr
    _ = (p : ℝ) ^ 2 * (2 / Real.sqrt (M : ℝ)) ^ p := by
        rw [show (2 : ℝ) / Real.sqrt (M : ℝ) = 2 * (1 / Real.sqrt (M : ℝ)) by ring, mul_pow]
        ring

/-- Third term: the probability that some small set meets all the kept sets. -/
theorem term3_tendsto (M : ℕ) (hM5 : 5 ≤ M) (C : ℕ) :
    Tendsto (fun p : ℕ => ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1))
        * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2)) atTop (𝓝 0) := by
  set η : ℝ := (1 / (M : ℝ)) ^ (4 * C + 3) with hη
  have hη0 : 0 < η := eta_pos M hM5 C
  have hη1 : η < 1 := eta_lt_one M hM5 C
  set r : ℝ := 1 - η with hr
  have hr0 : 0 < r := by simp only [hr]; linarith
  have hr1 : r < 1 := by simp only [hr]; linarith
  set t : ℝ := Real.sqrt r with ht
  have ht0 : 0 < t := by
    simp only [ht]
    exact Real.sqrt_pos.2 hr0
  have htr : t ^ 2 = r := Real.sq_sqrt hr0.le
  have ht1 : t < 1 := by
    nlinarith [htr, ht0]
  set K : ℕ := 2 * (C + 1) with hK
  -- Step B : the term is at most `(Q p * r ^ (p / 2)) ^ p`.
  have stepB : ∀ p : ℕ, ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1)) * r ^ (p ^ 2 / 2)
      ≤ (((p : ℝ) ^ 2 + 1) ^ K * r ^ (p / 2)) ^ p := by
    intro p
    have hexp : 2 * p * (C + 1) = K * p := by simp only [hK]; ring
    have hdiv : p / 2 * p ≤ p ^ 2 / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h2 : 2 * (p / 2) ≤ p := by omega
      calc p / 2 * p * 2 = p * (2 * (p / 2)) := by ring
        _ ≤ p * p := Nat.mul_le_mul_left p h2
        _ = p ^ 2 := by ring
    have hpow : r ^ (p ^ 2 / 2) ≤ (r ^ (p / 2)) ^ p := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one hr0.le hr1.le hdiv
    calc ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1)) * r ^ (p ^ 2 / 2)
        = (((p : ℝ) ^ 2 + 1) ^ K) ^ p * r ^ (p ^ 2 / 2) := by
          rw [hexp, pow_mul]
      _ ≤ (((p : ℝ) ^ 2 + 1) ^ K) ^ p * (r ^ (p / 2)) ^ p :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (((p : ℝ) ^ 2 + 1) ^ K * r ^ (p / 2)) ^ p := by rw [mul_pow]
  -- Step C : eventually `Q p * r ^ (p / 2) ≤ 1 / 2`.
  have majtendsto : Tendsto (fun p : ℕ => 2 ^ K / t * ((p : ℝ) ^ (2 * K) * t ^ p))
      atTop (𝓝 0) := by
    have := tendsto_pow_const_mul_const_pow_of_lt_one (2 * K) ht0.le ht1
    simpa using this.const_mul (2 ^ K / t)
  have hmaj : ∀ᶠ p : ℕ in atTop, 2 ^ K / t * ((p : ℝ) ^ (2 * K) * t ^ p) < 1 / 2 :=
    majtendsto.eventually_lt_const (by norm_num)
  have hone : ∀ᶠ p : ℕ in atTop, 1 ≤ p := eventually_ge_atTop 1
  have stepC : ∀ᶠ p : ℕ in atTop, ((p : ℝ) ^ 2 + 1) ^ K * r ^ (p / 2) ≤ 1 / 2 := by
    filter_upwards [hmaj, hone] with p hp hp1
    have hple : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    -- bound the polynomial factor
    have hQ : ((p : ℝ) ^ 2 + 1) ^ K ≤ 2 ^ K * (p : ℝ) ^ (2 * K) := by
      have h1 : (p : ℝ) ^ 2 + 1 ≤ 2 * (p : ℝ) ^ 2 := by nlinarith
      calc ((p : ℝ) ^ 2 + 1) ^ K ≤ (2 * (p : ℝ) ^ 2) ^ K :=
            pow_le_pow_left₀ (by positivity) h1 K
        _ = 2 ^ K * (p : ℝ) ^ (2 * K) := by
            rw [mul_pow, ← pow_mul, mul_comm 2 K]
    -- bound the geometric factor
    have hgeo : r ^ (p / 2) ≤ t ^ p / t := by
      have hle : p - 1 ≤ 2 * (p / 2) := by omega
      have h1 : r ^ (p / 2) = t ^ (2 * (p / 2)) := by
        rw [← htr, ← pow_mul]
      have h2 : t ^ (2 * (p / 2)) ≤ t ^ (p - 1) :=
        pow_le_pow_of_le_one ht0.le ht1.le hle
      have h3 : t ^ (p - 1) = t ^ p / t := by
        rw [eq_div_iff ht0.ne', ← pow_succ]
        congr 1
        omega
      rw [h1, ← h3]
      exact h2
    calc ((p : ℝ) ^ 2 + 1) ^ K * r ^ (p / 2)
        ≤ (2 ^ K * (p : ℝ) ^ (2 * K)) * (t ^ p / t) :=
          mul_le_mul hQ hgeo (pow_nonneg hr0.le _) (by positivity)
      _ = 2 ^ K / t * ((p : ℝ) ^ (2 * K) * t ^ p) := by
          field_simp
      _ ≤ 1 / 2 := le_of_lt hp
  -- Step D : squeeze between `0` and `(1/2) ^ p`.
  refine squeeze_zero' (Eventually.of_forall (fun p => ?_)) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1))
  · exact mul_nonneg (by positivity) (pow_nonneg hr0.le _)
  · filter_upwards [stepC] with p hp
    refine le_trans (stepB p) ?_
    exact pow_le_pow_left₀ (by positivity) hp p

/-! ### The main estimate -/

/-- For `0 ≤ c₀ < 1`, `M ≥ 5` with `M ^ (1 - c₀) > 2`, and any `C`, the total failure
probability is `< 1` for all large `p`. -/
theorem eventually_sum_lt_one (c₀ : ℝ) (h0 : 0 ≤ c₀) (hc : c₀ < 1) (M : ℕ) (hM5 : 5 ≤ M)
    (hM : (2 : ℝ) < (M : ℝ) ^ (1 - c₀)) (C : ℕ) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p →
      (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ (⌊c₀ * p⌋₊) / (M : ℝ) ^ p
        + (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ (p / 2) / (M : ℝ) ^ p
        + ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1)) * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2)
      < 1 := by
  have h : Tendsto (fun p : ℕ =>
      (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ (⌊c₀ * p⌋₊) / (M : ℝ) ^ p
        + (p : ℝ) ^ 2 * 2 ^ p * (M : ℝ) ^ (p / 2) / (M : ℝ) ^ p
        + ((p : ℝ) ^ 2 + 1) ^ (2 * p * (C + 1))
            * (1 - (1 / (M : ℝ)) ^ (4 * C + 3)) ^ (p ^ 2 / 2)) atTop (𝓝 0) := by
    have h12 := (term1_tendsto c₀ h0 hc M hM5 hM).add (term2_tendsto M hM5)
    have h123 := h12.add (term3_tendsto M hM5 C)
    simpa using h123
  exact Filter.eventually_atTop.1 (h.eventually_lt_const (by norm_num))

end Erdos664
