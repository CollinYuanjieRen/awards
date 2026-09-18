import MerLeanExperiment.TruncatedExponential

/-!
# The normalized first-power-sum scale

This is the sequential form of Luo--Yang--Zhu Lemma 2.2. A strictly
increasing sequence of counterexample sizes is the exact data extracted from
the negation of the eventual theorem.
-/

open Filter Finset
open scoped Topology
namespace Erdos973


private theorem factorial_power_ratio_le {N ell : ℕ} (hell : ell ≤ N)
    {x : ℝ} (hx : 0 < x) :
    (x ^ (N - ell) / (N - ell).factorial) /
        (x ^ N / N.factorial) ≤ ((N : ℝ) / x) ^ ell := by
  have hpow : x ^ N = x ^ (N - ell) * x ^ ell := by
    rw [← pow_add, Nat.sub_add_cancel hell]
  have hfac : ((N - ell).factorial : ℝ) * N.descFactorial ell = N.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hell
  rw [hpow, ← hfac]
  field_simp
  have hcancel : x ^ ell * ((N : ℝ) / x) ^ ell = (N : ℝ) ^ ell := by
    rw [div_pow]
    field_simp
  rw [hcancel]
  exact_mod_cast Nat.descFactorial_le_pow N ell

private theorem top_coefficient_geometric_bound {n : ℕ} (z : Fin n → ℂ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsmall : ∀ k ∈ Finset.Icc 2 (n + 1), ‖powerSum z k‖ ≤ epsilon)
    (hx : 0 < ‖-powerSum z 1‖) :
    1 ≤ Real.exp (epsilon * perturbationMajorant n ((n + 1 : ℕ) / ‖-powerSum z 1‖)) - 1 := by
  let X : ℂ := -powerSum z 1
  let q : ℝ := (n + 1 : ℕ) / ‖X‖
  let f : ℕ → ℂ := fun ell ↦ perturbationCoeff z ell * X ^ (n + 1 - ell) /
    ((n + 1 - ell).factorial : ℂ)
  have hcoeff : (rootProduct z).coeff (n + 1) = 0 :=
    coeff_rootProduct_eq_zero_of_lt z (by omega)
  have hconv := rootProduct_coeff_eq_truncated_convolution z (m := n + 1) (by omega)
  have hsum : ∑ ell ∈ range (n + 2), f ell = 0 := by
    rw [hcoeff] at hconv
    simpa [f, X, Nat.add_assoc] using hconv.symm
  have hsplit : ∑ ell ∈ range (n + 2), f ell = f 0 + f 1 + ∑ i ∈ range n, f (2 + i) := by
    rw [show n + 2 = 2 + n by omega, sum_range_add]
    simp [sum_range_succ, add_assoc]
  have hf0 : f 0 = X ^ (n + 1) / ((n + 1).factorial : ℂ) := by
    simp [f, perturbationCoeff_zero]
  have hf1 : f 1 = 0 := by simp [f, perturbationCoeff_one]
  have htail : f 0 = -∑ i ∈ range n, f (2 + i) := by
    rw [hsplit, hf1, add_zero] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  have hf0pos : 0 < ‖f 0‖ := by
    rw [hf0, norm_div, Complex.norm_pow, Complex.norm_natCast]
    positivity
  have hnorm : ‖f 0‖ ≤ ∑ i ∈ range n, ‖f (2 + i)‖ := by
    rw [htail, norm_neg]
    exact norm_sum_le _ _
  have hone : (1 : ℝ) ≤ ∑ i ∈ range n, ‖f (2 + i)‖ / ‖f 0‖ := by
    rw [← sum_div]
    have := (div_le_div_iff_of_pos_right hf0pos).2 hnorm
    simpa [ne_of_gt hf0pos] using this
  calc
    (1 : ℝ) ≤ ∑ i ∈ range n, ‖f (2 + i)‖ / ‖f 0‖ := hone
    _ ≤ ∑ i ∈ range n, ‖perturbationCoeff z (2 + i)‖ * q ^ (2 + i) := by
      gcongr with i hi
      have hi' := mem_range.mp hi
      have hiN : 2 + i ≤ n + 1 := by omega
      rw [hf0]
      simp only [f, norm_div, norm_mul, Complex.norm_pow, Complex.norm_natCast]
      calc
        _ = ‖perturbationCoeff z (2 + i)‖ *
            ((‖X‖ ^ (n + 1 - (2 + i)) / (n + 1 - (2 + i)).factorial) /
              (‖X‖ ^ (n + 1) / (n + 1).factorial)) := by ring
        _ ≤ ‖perturbationCoeff z (2 + i)‖ * q ^ (2 + i) := by
          gcongr
          exact factorial_power_ratio_le hiN hx
    _ ≤ ∑' ell : ℕ, if 2 ≤ ell then ‖perturbationCoeff z ell‖ * q ^ ell else 0 := by
      let g : ℕ → ℝ := fun ell ↦
        if 2 ≤ ell then ‖perturbationCoeff z ell‖ * q ^ ell else 0
      have hsum_eq : ∑ i ∈ range n, ‖perturbationCoeff z (2 + i)‖ * q ^ (2 + i) =
          ∑ ell ∈ Ico 2 (n + 2), g ell := by
        rw [sum_Ico_eq_sum_range]
        simp [g]
      rw [hsum_eq]
      apply Summable.sum_le_tsum
      · intro i hi
        positivity
      · have hs :=
          (summable_perturbationCoeff_norm_mul_pow z q).indicator {ell : ℕ | 2 ≤ ell}
        change Summable g
        rw [show g = {ell : ℕ | 2 ≤ ell}.indicator
            (fun ell ↦ ‖perturbationCoeff z ell‖ * q ^ ell) by
          funext ell
          simp only [g, Set.indicator, Set.mem_setOf_eq]]
        exact hs
    _ ≤ Real.exp (epsilon * perturbationMajorant n q) - 1 :=
      perturbationCoeff_majorant z hepsilon (by positivity) hsmall
    _ = _ := by rfl


private theorem top_coefficient_exponential_bound {n : ℕ} (z : Fin n → ℂ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsmall : ∀ k ∈ Finset.Icc 2 (n + 1), ‖powerSum z k‖ ≤ epsilon) :
    ‖-powerSum z 1‖ ^ (n + 1) / (n + 1).factorial ≤
      Real.exp ‖-powerSum z 1‖ *
        (Real.exp (epsilon * perturbationMajorant n 1) - 1) := by
  let X : ℂ := -powerSum z 1
  let f : ℕ → ℂ := fun ell ↦ perturbationCoeff z ell * X ^ (n + 1 - ell) /
    ((n + 1 - ell).factorial : ℂ)
  have hcoeff : (rootProduct z).coeff (n + 1) = 0 :=
    coeff_rootProduct_eq_zero_of_lt z (by omega)
  have hconv := rootProduct_coeff_eq_truncated_convolution z (m := n + 1) (by omega)
  have hsum : ∑ ell ∈ range (n + 2), f ell = 0 := by
    rw [hcoeff] at hconv
    simpa [f, X, Nat.add_assoc] using hconv.symm
  have hsplit : ∑ ell ∈ range (n + 2), f ell =
      f 0 + f 1 + ∑ i ∈ range n, f (2 + i) := by
    rw [show n + 2 = 2 + n by omega, sum_range_add]
    simp [sum_range_succ, add_assoc]
  have hf0 : f 0 = X ^ (n + 1) / ((n + 1).factorial : ℂ) := by
    simp [f, perturbationCoeff_zero]
  have hf1 : f 1 = 0 := by simp [f, perturbationCoeff_one]
  have htail : f 0 = -∑ i ∈ range n, f (2 + i) := by
    rw [hsplit, hf1, add_zero] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  calc
    ‖-powerSum z 1‖ ^ (n + 1) / (n + 1).factorial = ‖f 0‖ := by
      rw [hf0]
      simp [X]
    _ ≤ ∑ i ∈ range n, ‖f (2 + i)‖ := by
      rw [htail, norm_neg]
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ range n,
        ‖perturbationCoeff z (2 + i)‖ * Real.exp ‖X‖ := by
      gcongr with i hi
      simp only [f, norm_div, norm_mul, Complex.norm_pow, Complex.norm_natCast]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (Real.pow_div_factorial_le_exp ‖X‖ (norm_nonneg X) (n + 1 - (2 + i)))
        (norm_nonneg (perturbationCoeff z (2 + i)))
    _ = Real.exp ‖X‖ *
        ∑ i ∈ range n, ‖perturbationCoeff z (2 + i)‖ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ Real.exp ‖X‖ *
        (∑' ell : ℕ, if 2 ≤ ell then ‖perturbationCoeff z ell‖ else 0) := by
      gcongr
      let g : ℕ → ℝ := fun ell ↦ if 2 ≤ ell then ‖perturbationCoeff z ell‖ else 0
      have hsum_eq : ∑ i ∈ range n, ‖perturbationCoeff z (2 + i)‖ =
          ∑ ell ∈ Ico 2 (n + 2), g ell := by
        rw [sum_Ico_eq_sum_range]
        simp [g]
      rw [hsum_eq]
      apply Summable.sum_le_tsum
      · intro i hi
        positivity
      · have hs := (summable_perturbationCoeff_norm_mul_pow z 1).indicator
          {ell : ℕ | 2 ≤ ell}
        change Summable g
        rw [show g = {ell : ℕ | 2 ≤ ell}.indicator
            (fun ell ↦ ‖perturbationCoeff z ell‖ * (1 : ℝ) ^ ell) by
          funext ell
          simp [g, Set.indicator]]
        exact hs
    _ ≤ Real.exp ‖X‖ *
        (Real.exp (epsilon * perturbationMajorant n 1) - 1) := by
      have hmaj : (∑' ell : ℕ,
          if 2 ≤ ell then ‖perturbationCoeff z ell‖ else 0) ≤
          Real.exp (epsilon * perturbationMajorant n 1) - 1 := by
        simpa using perturbationCoeff_majorant z (R := 1) hepsilon (by norm_num) hsmall
      exact mul_le_mul_of_nonneg_left hmaj (Real.exp_pos ‖X‖).le
    _ = _ := by rfl


open Polynomial

private theorem coeff_rootProduct_top {n : ℕ} (z : Fin n → ℂ) :
    (rootProduct z).coeff n = ∏ j, (-z j) := by
  rw [rootProduct]
  have hdeg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      (1 - C (z j) * X : ℂ[X]).natDegree ≤ 1 := by
    intro j hj
    apply natDegree_le_iff_degree_le.mpr
    apply (degree_sub_le _ _).trans
    apply max_le (by simp)
    apply (degree_mul_le _ _).trans
    calc
      (C (z j)).degree + X.degree ≤ 0 + 1 := add_le_add degree_C_le (by rw [degree_X])
      _ = 1 := by simp
  have h := coeff_prod_of_natDegree_le (Finset.univ : Finset (Fin n))
      (fun j => (1 - C (z j) * X : ℂ[X])) 1 hdeg
  have h' : (∏ i, (1 - C (z i) * X : ℂ[X])).coeff n =
      ∏ i, (1 - C (z i) * X : ℂ[X]).coeff 1 := by simpa using h
  rw [h']
  apply prod_congr rfl
  intro j hj
  norm_num [coeff_sub, coeff_one, coeff_C_mul_X]

private theorem one_le_norm_coeff_rootProduct_top {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ j, 1 ≤ ‖z j‖) : 1 ≤ ‖(rootProduct z).coeff n‖ := by
  rw [coeff_rootProduct_top, norm_prod]
  simpa using Finset.one_le_prod (fun j _ ↦ by simpa using hz j)


private theorem leading_coefficient_exponential_bound {n : ℕ} (hn : 1 ≤ n)
    (z : Fin n → ℂ) (hz : ∀ j, 1 ≤ ‖z j‖)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsmall : ∀ k ∈ Finset.Icc 2 (n + 1), ‖powerSum z k‖ ≤ epsilon) :
    1 ≤ ‖-powerSum z 1‖ ^ n / n.factorial +
      Real.exp ‖-powerSum z 1‖ *
        (Real.exp (epsilon * perturbationMajorant n 1) - 1) := by
  let X : ℂ := -powerSum z 1
  let f : ℕ → ℂ := fun ell ↦ perturbationCoeff z ell * X ^ (n - ell) /
    ((n - ell).factorial : ℂ)
  have hconv := rootProduct_coeff_eq_truncated_convolution z (m := n) (by omega)
  have hnorm : ‖(rootProduct z).coeff n‖ ≤ ∑ ell ∈ range (n + 1), ‖f ell‖ := by
    rw [hconv]
    exact norm_sum_le _ _
  have hsplit : ∑ ell ∈ range (n + 1), ‖f ell‖ =
      ‖f 0‖ + ‖f 1‖ + ∑ i ∈ range (n - 1), ‖f (2 + i)‖ := by
    rw [show n + 1 = 2 + (n - 1) by omega, sum_range_add]
    simp [sum_range_succ, add_assoc]
  have hf0 : ‖f 0‖ = ‖X‖ ^ n / n.factorial := by
    simp [f, perturbationCoeff_zero]
  have hf1 : ‖f 1‖ = 0 := by simp [f, perturbationCoeff_one]
  calc
    (1 : ℝ) ≤ ‖(rootProduct z).coeff n‖ := one_le_norm_coeff_rootProduct_top z hz
    _ ≤ ∑ ell ∈ range (n + 1), ‖f ell‖ := hnorm
    _ = ‖X‖ ^ n / n.factorial + ∑ i ∈ range (n - 1), ‖f (2 + i)‖ := by
      rw [hsplit, hf0, hf1, add_zero]
    _ ≤ ‖X‖ ^ n / n.factorial +
        ∑ i ∈ range (n - 1),
          ‖perturbationCoeff z (2 + i)‖ * Real.exp ‖X‖ := by
      gcongr with i hi
      simp only [f, norm_div, norm_mul, Complex.norm_pow, Complex.norm_natCast]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (Real.pow_div_factorial_le_exp ‖X‖ (norm_nonneg X) (n - (2 + i)))
        (norm_nonneg (perturbationCoeff z (2 + i)))
    _ = ‖X‖ ^ n / n.factorial + Real.exp ‖X‖ *
        ∑ i ∈ range (n - 1), ‖perturbationCoeff z (2 + i)‖ := by
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ ‖X‖ ^ n / n.factorial + Real.exp ‖X‖ *
        (∑' ell : ℕ, if 2 ≤ ell then ‖perturbationCoeff z ell‖ else 0) := by
      gcongr
      let g : ℕ → ℝ := fun ell ↦ if 2 ≤ ell then ‖perturbationCoeff z ell‖ else 0
      have hsum_eq : ∑ i ∈ range (n - 1), ‖perturbationCoeff z (2 + i)‖ =
          ∑ ell ∈ Ico 2 (n + 1), g ell := by
        rw [sum_Ico_eq_sum_range]
        simp [g]
      rw [hsum_eq]
      apply Summable.sum_le_tsum
      · intro i hi
        positivity
      · have hs := (summable_perturbationCoeff_norm_mul_pow z 1).indicator
          {ell : ℕ | 2 ≤ ell}
        change Summable g
        rw [show g = {ell : ℕ | 2 ≤ ell}.indicator
            (fun ell ↦ ‖perturbationCoeff z ell‖ * (1 : ℝ) ^ ell) by
          funext ell
          simp [g, Set.indicator]]
        exact hs
    _ ≤ ‖X‖ ^ n / n.factorial + Real.exp ‖X‖ *
        (Real.exp (epsilon * perturbationMajorant n 1) - 1) := by
      have hmaj : (∑' ell : ℕ,
          if 2 ≤ ell then ‖perturbationCoeff z ell‖ else 0) ≤
          Real.exp (epsilon * perturbationMajorant n 1) - 1 := by
        simpa using perturbationCoeff_majorant z (R := 1) hepsilon (by norm_num) hsmall
      gcongr
    _ = _ := by rfl


private theorem perturbationMajorant_bound (n : ℕ) {q q₀ : ℝ}
    (hq : 0 ≤ q) (hqq : q ≤ q₀) (hq₀ : q₀ < 1) :
    perturbationMajorant n q ≤ (1 - q₀)⁻¹ := by
  unfold perturbationMajorant
  calc
    (∑ k ∈ Icc 2 (n + 1), q ^ k / k) ≤ ∑ k ∈ Icc 2 (n + 1), q₀ ^ k := by
      gcongr with k hk
      have hk2 := (mem_Icc.mp hk).1
      have hq₀nonneg : 0 ≤ q₀ := hq.trans hqq
      calc
        q ^ k / (k : ℝ) ≤ q ^ k :=
          div_le_self (pow_nonneg hq k) (by exact_mod_cast (show 1 ≤ k by omega))
        _ ≤ q₀ ^ k := pow_le_pow_left₀ hq hqq k
    _ ≤ ∑' k : ℕ, q₀ ^ k := by
      exact (summable_geometric_of_lt_one (hq.trans hqq) hq₀).sum_le_tsum _
        (fun i _ ↦ pow_nonneg (hq.trans hqq) i)
    _ = (1 - q₀)⁻¹ := tsum_geometric_of_lt_one (hq.trans hqq) hq₀


private theorem perturbationMajorant_one_le (n : ℕ) :
    perturbationMajorant n 1 ≤ n := by
  unfold perturbationMajorant
  calc
    (∑ k ∈ Icc 2 (n + 1), (1 : ℝ) ^ k / k) ≤
        ∑ _k ∈ Icc 2 (n + 1), (1 : ℝ) := by
      gcongr with k hk
      have hk2 := (mem_Icc.mp hk).1
      norm_num
      exact (inv_le_one₀ (by positivity)).2
        (by exact_mod_cast (show 1 ≤ k by omega))
    _ = ((Icc 2 (n + 1)).card : ℝ) := by simp
    _ ≤ n := by norm_cast; simp

private theorem scaled_pow_div_factorial_le (q : ℝ) (hq : 0 ≤ q)
    {n : ℕ} (hn : 0 < n) :
    (q * n) ^ n / n.factorial ≤ (Real.exp 1 * q) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : (1 : ℝ) ≤ √(2 * Real.pi * n) := by
    rw [Real.one_le_sqrt]
    calc
      (1 : ℝ) ≤ 2 * 2 * 1 := by norm_num
      _ ≤ 2 * Real.pi * n := by
        gcongr
        · exact Real.two_le_pi
        · exact_mod_cast hn
  have hfac : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) :=
    (le_mul_of_one_le_left (pow_nonneg (by positivity) n) hsqrt).trans
      (Stirling.le_factorial_stirling n)
  calc
    (q * n) ^ n / n.factorial ≤
        (q * n) ^ n / ((n : ℝ) / Real.exp 1) ^ n := by
      exact div_le_div_of_nonneg_left (pow_nonneg (mul_nonneg hq hnR.le) n)
        (pow_pos (by positivity) n) hfac
    _ = (Real.exp 1 * q) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp


private theorem tendsto_log_factorial_normalized :
    Tendsto (fun n : ℕ ↦
      (Real.log (n.factorial : ℝ) - n * Real.log n) / n)
      atTop (𝓝 (-1)) := by
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hstir : Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq n))
      atTop (𝓝 (Real.log (√Real.pi))) := by
    exact (Real.continuousAt_log (by positivity)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hstirdiv : Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq n) / n)
      atTop (𝓝 0) := hstir.div_atTop hnat
  have hlogdiv : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n)
      atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hlog2div : Tendsto (fun n : ℕ ↦ Real.log (2 * (n : ℝ)) / n)
      atTop (𝓝 0) := by
    have hconstdiv : Tendsto (fun n : ℕ ↦ Real.log 2 / (n : ℝ))
        atTop (𝓝 0) :=
      (show Tendsto (fun _ : ℕ ↦ Real.log 2) atTop (𝓝 (Real.log 2)) from
        tendsto_const_nhds).div_atTop hnat
    have hsum := hconstdiv.add hlogdiv
    simpa only [zero_add] using hsum.congr' (by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
      ring)
  have hcalc : Tendsto (fun n : ℕ ↦
      Real.log (Stirling.stirlingSeq n) / n +
        (1 / 2 : ℝ) * (Real.log (2 * (n : ℝ)) / n) - 1)
      atTop (𝓝 (-1)) := by
    have ht := (hstirdiv.add (hlog2div.const_mul (1 / 2))).sub_const 1
    simpa using ht
  apply hcalc.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [Stirling.log_stirlingSeq_formula]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_div (by positivity) (by positivity), Real.log_exp]
  field_simp
  ring



private theorem tendsto_log_scaled_power_div_factorial (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (r : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (hr : Tendsto r atTop (𝓝 a)) :
    Tendsto (fun m ↦ Real.log (((N m : ℝ) * r m) ^ (N m + 1) /
        ((N m + 1).factorial : ℝ)) / (N m : ℝ)) atTop (𝓝 (1 + Real.log a)) := by
  have hNR : Tendsto (fun m ↦ (N m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hK : Tendsto (fun m ↦ N m + 1) atTop atTop :=
    tendsto_atTop_mono (fun m ↦ Nat.le_add_right (N m) 1) hN
  have hKR : Tendsto (fun m ↦ (↑(N m + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hK
  have hratio : Tendsto (fun m ↦ ((N m + 1 : ℕ) : ℝ) / (N m : ℝ))
      atTop (𝓝 1) := by
    have hi : Tendsto (fun m ↦ ((N m : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hNR
    have ht := (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) from
      tendsto_const_nhds).add hi
    simpa only [add_zero] using ht.congr' (by
      filter_upwards [hN.eventually (eventually_ge_atTop 1)] with m hm
      rw [Nat.cast_add, Nat.cast_one]
      field_simp)
  have hNoverK : Tendsto (fun m ↦ (N m : ℝ) / ((N m + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    have hi := hratio.inv₀ (by norm_num)
    simpa only [inv_div, inv_one] using hi
  have hlogNoverK := hNoverK.log (by norm_num : (1 : ℝ) ≠ 0)
  have hlogr := hr.log (ne_of_gt ha)
  have hfac := tendsto_log_factorial_normalized.comp hK
  have hbracket : Tendsto (fun m ↦ Real.log (r m) +
        Real.log ((N m : ℝ) / ((N m + 1 : ℕ) : ℝ)) -
        (Real.log (((N m + 1).factorial : ℝ)) -
          ((N m + 1 : ℕ) : ℝ) * Real.log ((N m + 1 : ℕ) : ℝ)) /
          ((N m + 1 : ℕ) : ℝ)) atTop (𝓝 (1 + Real.log a)) := by
    have ht := (hlogr.add hlogNoverK).sub hfac
    simpa [Function.comp_def, Real.log_one, add_comm, add_left_comm, add_assoc] using ht
  have ht := hratio.mul hbracket
  apply (show Tendsto (fun m ↦ ((N m + 1 : ℕ) : ℝ) / (N m : ℝ) *
      (Real.log (r m) + Real.log ((N m : ℝ) / ((N m + 1 : ℕ) : ℝ)) -
        (Real.log (((N m + 1).factorial : ℝ)) -
          ((N m + 1 : ℕ) : ℝ) * Real.log ((N m + 1 : ℕ) : ℝ)) /
          ((N m + 1 : ℕ) : ℝ))) atTop (𝓝 (1 + Real.log a)) by simpa using ht).congr'
  filter_upwards [hN.eventually (eventually_ge_atTop 1),
    tendsto_const_nhds.eventually_lt hr ha] with m hm hrm
  have hNr : 0 < (N m : ℝ) * r m := mul_pos (by exact_mod_cast hm) hrm
  have hloglhs : Real.log (((N m : ℝ) * r m) ^ (N m + 1) /
      ((N m + 1).factorial : ℝ)) =
      ((N m + 1 : ℕ) : ℝ) * Real.log ((N m : ℝ) * r m) -
        Real.log (((N m + 1).factorial : ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  rw [hloglhs, Real.log_mul (by positivity) (ne_of_gt hrm),
    Real.log_div (by positivity) (by positivity)]
  field_simp
  ring


/-- Luo--Yang--Zhu Lemma 2.2: counterexamples with all controlled power sums
exponentially small have, after a subsequence, a nonzero normalized first sum
of norm strictly below one and satisfying the sharp scalar inequality. -/
theorem normalized_first_sum_scale
    {lambda : ℝ} (hlambda : 0 < lambda)
    (size : ℕ → ℕ) (hsize : StrictMono size)
    (z : ∀ m, Fin (size m) → ℂ)
    (hzext : ∀ m j, 1 ≤ ‖z m j‖)
    (hsmall : ∀ m k, k ∈ Finset.Icc 2 (size m + 1) →
      ‖powerSum (z m) k‖ ≤ Real.exp (-lambda * size m)) :
    ∃ (phi : ℕ → ℕ) (c : ℂ), StrictMono phi ∧
      Tendsto (fun m =>
        (-powerSum (z (phi m)) 1) / ((size (phi m) : ℕ) : ℂ))
        atTop (𝓝 c) ∧
      0 < ‖c‖ ∧ ‖c‖ < 1 ∧
      lambda ≤ ‖c‖ - 1 - Real.log ‖c‖ := by
  let X : ℕ → ℂ := fun m ↦ -powerSum (z m) 1
  let y : ℕ → ℂ := fun m ↦ X m / ((size m : ℕ) : ℂ)
  have hsizeR : Tendsto (fun m ↦ (size m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize.tendsto_atTop
  have heps : Tendsto (fun m ↦ Real.exp (-lambda * size m) * 4) atTop (𝓝 0) := by
    have hlin : Tendsto (fun m ↦ lambda * (size m : ℝ)) atTop atTop :=
      hsizeR.const_mul_atTop hlambda
    simpa [neg_mul, mul_comm] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).mul_const 4
  have hexpsmall : ∀ᶠ m : ℕ in atTop,
      Real.exp (Real.exp (-lambda * size m) * 4) - 1 < 1 := by
    have ht : Tendsto (fun m ↦ Real.exp (Real.exp (-lambda * size m) * 4) - 1)
        atTop (𝓝 0) := by
      simpa using ((Real.continuous_exp.tendsto 0).comp heps).sub_const 1
    exact ht.eventually_lt_const zero_lt_one
  have hybound : ∀ᶠ m : ℕ in atTop, ‖y m‖ ≤ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 2, hexpsmall] with m hm hexp
    by_contra hnot
    have hy2 : 2 < ‖y m‖ := lt_of_not_ge hnot
    have hNm : 2 ≤ size m := le_trans hm (hsize.le_apply)
    have hNpos : (0 : ℝ) < size m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hNm)
    have hy_norm : ‖y m‖ = ‖X m‖ / size m := by
      simp [y, Complex.norm_natCast]
    have hXpos : 0 < ‖X m‖ := by
      apply norm_pos_iff.mpr
      intro hzero
      rw [hy_norm, hzero, norm_zero, zero_div] at hy2
      norm_num at hy2
    let q : ℝ := (size m + 1 : ℕ) / ‖X m‖
    have hq0 : 0 ≤ q := by positivity
    have hq : q ≤ (3 / 4 : ℝ) := by
      dsimp [q]
      rw [hy_norm] at hy2
      rw [div_le_iff₀ hXpos]
      have hNmR : (2 : ℝ) ≤ size m := by exact_mod_cast hNm
      have hlarge : 2 * (size m : ℝ) < ‖X m‖ :=
        (lt_div_iff₀ hNpos).mp hy2
      norm_num
      push_cast
      have hhalf : (size m : ℝ) + 1 ≤ (3 / 2 : ℝ) * size m := by linarith
      have hthree : (3 / 2 : ℝ) * size m < (3 / 4 : ℝ) * ‖X m‖ := by linarith
      linarith
    have hb : perturbationMajorant (size m) q ≤ 4 := by
      have := perturbationMajorant_bound (size m) hq0 hq (by norm_num : (3 / 4 : ℝ) < 1)
      norm_num at this ⊢
      exact this
    have htop := top_coefficient_geometric_bound (z m)
      (show 0 ≤ Real.exp (-lambda * size m) by positivity) (hsmall m) hXpos
    have harg : Real.exp (-lambda * size m) * perturbationMajorant (size m) q ≤
        Real.exp (-lambda * size m) * 4 := by gcongr
    have hexple : Real.exp (Real.exp (-lambda * size m) * perturbationMajorant (size m) q) - 1 ≤
        Real.exp (Real.exp (-lambda * size m) * 4) - 1 := by
      gcongr
    have hqdef : q = (size m + 1 : ℕ) / ‖-powerSum (z m) 1‖ := by rfl
    rw [← hqdef] at htop
    linarith
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hybound
  let ys : ℕ → ℂ := fun m ↦ y (M + m)
  have hys : ∀ m, ys m ∈ Metric.closedBall (0 : ℂ) 2 := by
    intro m
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hM (M + m) (Nat.le_add_right M m)
  obtain ⟨c, hcball, psi, hpsi, hpsilim⟩ :=
    (isCompact_closedBall (0 : ℂ) 2).tendsto_subseq hys
  let phi : ℕ → ℕ := fun m ↦ M + psi m
  have hphi : StrictMono phi := hpsi.const_add M
  have hylim : Tendsto (fun m ↦ y (phi m)) atTop (𝓝 c) := by
    simpa [ys, phi, Function.comp_def] using hpsilim
  have hc2 : ‖c‖ ≤ 2 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hcball
  have hc_le_one : ‖c‖ ≤ 1 := by
    by_contra hcnot
    have hc1 : 1 < ‖c‖ := lt_of_not_ge hcnot
    have hcpos : 0 < ‖c‖ := lt_trans zero_lt_one hc1
    let q₀ : ℝ := (1 + ‖c‖⁻¹) / 2
    have hcinv : ‖c‖⁻¹ < 1 := (inv_lt_one₀ hcpos).mpr hc1
    have hq₀lt : q₀ < 1 := by dsimp [q₀]; linarith
    have hq₀pos : 0 < q₀ := by dsimp [q₀]; positivity
    have hNphi : Tendsto (fun m ↦ (size (phi m) : ℝ)) atTop atTop :=
      hsizeR.comp hphi.tendsto_atTop
    have hNinv : Tendsto (fun m ↦ ((size (phi m) : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hNphi
    have hnormlim : Tendsto (fun m ↦ ‖y (phi m)‖) atTop (𝓝 ‖c‖) := hylim.norm
    have hqseq : Tendsto
        (fun m ↦ (1 + ((size (phi m) : ℝ))⁻¹) / ‖y (phi m)‖)
        atTop (𝓝 ‖c‖⁻¹) := by
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have ht := (hone.add hNinv).div hnormlim (ne_of_gt hcpos)
      have hfun : ((fun x : ℕ ↦ (1 : ℝ) + (size (phi x) : ℝ)⁻¹) /
          (fun m : ℕ ↦ ‖y (phi m)‖)) =
          (fun m ↦ (1 + ((size (phi m) : ℝ))⁻¹) / ‖y (phi m)‖) := by
        funext m
        rfl
      rw [hfun] at ht
      simpa using ht
    have hqevent : ∀ᶠ m : ℕ in atTop,
        (1 + ((size (phi m) : ℝ))⁻¹) / ‖y (phi m)‖ < q₀ := by
      exact hqseq.eventually_lt_const (by dsimp [q₀]; linarith)
    have hypos : ∀ᶠ m : ℕ in atTop, 0 < ‖y (phi m)‖ :=
      tendsto_const_nhds.eventually_lt hnormlim hcpos
    have hepsphi : Tendsto (fun m ↦ Real.exp (-lambda * size (phi m)) * (1 - q₀)⁻¹)
        atTop (𝓝 0) := by
      have hlinphi : Tendsto (fun m ↦ lambda * (size (phi m) : ℝ)) atTop atTop :=
        hNphi.const_mul_atTop hlambda
      simpa [neg_mul, mul_comm] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinphi).mul_const (1 - q₀)⁻¹
    have hexpphi : ∀ᶠ m : ℕ in atTop,
        Real.exp (Real.exp (-lambda * size (phi m)) * (1 - q₀)⁻¹) - 1 < 1 := by
      have ht : Tendsto
          (fun m ↦ Real.exp (Real.exp (-lambda * size (phi m)) * (1 - q₀)⁻¹) - 1)
          atTop (𝓝 0) := by
        simpa using ((Real.continuous_exp.tendsto 0).comp hepsphi).sub_const 1
      exact ht.eventually_lt_const zero_lt_one
    have hall : ∀ᶠ m : ℕ in atTop,
        1 ≤ m ∧
        (1 + ((size (phi m) : ℝ))⁻¹) / ‖y (phi m)‖ < q₀ ∧
        0 < ‖y (phi m)‖ ∧
        Real.exp (Real.exp (-lambda * size (phi m)) * (1 - q₀)⁻¹) - 1 < 1 := by
      filter_upwards [Filter.eventually_ge_atTop 1, hqevent, hypos, hexpphi]
        with m hm hq hy hsmallExp
      exact ⟨hm, hq, hy, hsmallExp⟩
    obtain ⟨m, hm, hq, hy, hsmallExp⟩ := hall.exists
    have hNm : 1 ≤ size (phi m) :=
      le_trans hm (le_trans hphi.le_apply hsize.le_apply)
    have hNpos : (0 : ℝ) < size (phi m) := by exact_mod_cast hNm
    have hy_norm : ‖y (phi m)‖ = ‖X (phi m)‖ / size (phi m) := by simp [y]
    have hXpos : 0 < ‖X (phi m)‖ := by
      apply norm_pos_iff.mpr
      intro hzero
      rw [hy_norm, hzero, norm_zero, zero_div] at hy
      exact (lt_irrefl 0 hy)
    let q : ℝ := (size (phi m) + 1 : ℕ) / ‖X (phi m)‖
    have hqeq : q = (1 + ((size (phi m) : ℝ))⁻¹) / ‖y (phi m)‖ := by
      dsimp [q]
      rw [hy_norm]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp
    have hqnonneg : 0 ≤ q := by positivity
    have hqle : q ≤ q₀ := by rw [hqeq]; exact hq.le
    have hb := perturbationMajorant_bound (size (phi m)) hqnonneg hqle hq₀lt
    have htop := top_coefficient_geometric_bound (z (phi m))
      (show 0 ≤ Real.exp (-lambda * size (phi m)) by positivity) (hsmall (phi m)) hXpos
    have harg : Real.exp (-lambda * size (phi m)) * perturbationMajorant (size (phi m)) q ≤
        Real.exp (-lambda * size (phi m)) * (1 - q₀)⁻¹ := by gcongr
    have hexple : Real.exp (Real.exp (-lambda * size (phi m)) *
          perturbationMajorant (size (phi m)) q) - 1 ≤
        Real.exp (Real.exp (-lambda * size (phi m)) * (1 - q₀)⁻¹) - 1 := by
      gcongr
    have hqdef : q = (size (phi m) + 1 : ℕ) /
        ‖-powerSum (z (phi m)) 1‖ := by rfl
    rw [← hqdef] at htop
    linarith
  have hcpos : 0 < ‖c‖ := by
    by_contra hcnot
    have hc0 : ‖c‖ = 0 := le_antisymm (le_of_not_gt hcnot) (norm_nonneg c)
    have hnormzero : Tendsto (fun m ↦ ‖y (phi m)‖) atTop (𝓝 0) := by
      simpa [hc0] using hylim.norm
    have hNphi : Tendsto (fun m ↦ (size (phi m) : ℝ)) atTop atTop :=
      hsizeR.comp hphi.tendsto_atTop
    have hlinhalf : Tendsto (fun m ↦ (lambda / 2) * (size (phi m) : ℝ))
        atTop atTop := hNphi.const_mul_atTop (half_pos hlambda)
    have hdecay0 : Tendsto
        (fun m ↦ 2 * (size (phi m) : ℝ) *
          Real.exp (-(lambda / 2) * size (phi m))) atTop (𝓝 0) := by
      have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlinhalf
      have ht' := ht.mul_const (4 / lambda)
      convert ht' using 1 <;> simp [hlambda.ne']
      funext m
      field_simp
      ring
    have hdecay : ∀ᶠ m : ℕ in atTop,
        2 * (size (phi m) : ℝ) * Real.exp (-(lambda / 2) * size (phi m)) < 1 / 2 :=
      hdecay0.eventually_lt_const (by norm_num)
    have hbase0 : Tendsto (fun m ↦ Real.exp 1 * ‖y (phi m)‖) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hnormzero :
        Tendsto (fun m ↦ Real.exp 1 * ‖y (phi m)‖) atTop (𝓝 (Real.exp 1 * 0)))
    have hbase : ∀ᶠ m : ℕ in atTop, Real.exp 1 * ‖y (phi m)‖ ≤ 1 / 2 :=
      hbase0.eventually_le_const (by norm_num)
    have hylambda : ∀ᶠ m : ℕ in atTop, ‖y (phi m)‖ ≤ lambda / 2 :=
      hnormzero.eventually_le_const (half_pos hlambda)
    have htzero : Tendsto (fun m ↦ Real.exp (-lambda * size (phi m)) * size (phi m))
        atTop (𝓝 0) := by
      have hlin : Tendsto (fun m ↦ lambda * (size (phi m) : ℝ)) atTop atTop :=
        hNphi.const_mul_atTop hlambda
      have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
      have ht' := ht.mul_const lambda⁻¹
      convert ht' using 1 <;> simp [hlambda.ne']
      funext m
      field_simp
    have htsmall : ∀ᶠ m : ℕ in atTop,
        Real.exp (-lambda * size (phi m)) * size (phi m) ≤ 1 :=
      htzero.eventually_le_const zero_lt_one
    have hall : ∀ᶠ m : ℕ in atTop,
        1 ≤ m ∧ Real.exp 1 * ‖y (phi m)‖ ≤ 1 / 2 ∧
        ‖y (phi m)‖ ≤ lambda / 2 ∧
        Real.exp (-lambda * size (phi m)) * size (phi m) ≤ 1 ∧
        2 * (size (phi m) : ℝ) * Real.exp (-(lambda / 2) * size (phi m)) < 1 / 2 := by
      filter_upwards [Filter.eventually_ge_atTop 1, hbase, hylambda, htsmall, hdecay]
        with m hm hb hy ht hd
      exact ⟨hm, hb, hy, ht, hd⟩
    obtain ⟨m, hm, hbase_m, hylambda_m, ht_m, hdecay_m⟩ := hall.exists
    have hNm : 1 ≤ size (phi m) :=
      le_trans hm (le_trans hphi.le_apply hsize.le_apply)
    have hNpos : 0 < size (phi m) := lt_of_lt_of_le Nat.zero_lt_one hNm
    have hy_norm : ‖y (phi m)‖ = ‖X (phi m)‖ / size (phi m) := by simp [y]
    have hXnorm : ‖X (phi m)‖ = ‖y (phi m)‖ * size (phi m) := by
      rw [hy_norm, div_mul_cancel₀]
      exact_mod_cast (ne_of_gt hNpos)
    have hb1 := perturbationMajorant_one_le (size (phi m))
    have ht_nonneg : 0 ≤ Real.exp (-lambda * size (phi m)) *
        perturbationMajorant (size (phi m)) 1 := by
      apply mul_nonneg (Real.exp_pos _).le
      unfold perturbationMajorant
      positivity
    have ht_le_one : Real.exp (-lambda * size (phi m)) *
        perturbationMajorant (size (phi m)) 1 ≤ 1 :=
      (mul_le_mul_of_nonneg_left hb1 (Real.exp_pos _).le).trans ht_m
    have hexpdiff : Real.exp (Real.exp (-lambda * size (phi m)) *
          perturbationMajorant (size (phi m)) 1) - 1 ≤
        2 * (Real.exp (-lambda * size (phi m)) *
          perturbationMajorant (size (phi m)) 1) := by
      have habs := Real.abs_exp_sub_one_le
        (show |Real.exp (-lambda * size (phi m)) *
          perturbationMajorant (size (phi m)) 1| ≤ 1 by
          rw [abs_of_nonneg ht_nonneg]
          exact ht_le_one)
      rw [abs_of_nonneg ht_nonneg,
        abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht_nonneg))] at habs
      exact habs
    have hlead := leading_coefficient_exponential_bound hNm (z (phi m)) (hzext (phi m))
      (show 0 ≤ Real.exp (-lambda * size (phi m)) by positivity) (hsmall (phi m))
    have hfirst : ‖X (phi m)‖ ^ size (phi m) / (size (phi m)).factorial ≤ 1 / 2 := by
      calc
        _ = (‖y (phi m)‖ * size (phi m)) ^ size (phi m) /
            (size (phi m)).factorial := by rw [hXnorm]
        _ ≤ (Real.exp 1 * ‖y (phi m)‖) ^ size (phi m) :=
          scaled_pow_div_factorial_le _ (norm_nonneg _) hNpos
        _ ≤ (1 / 2 : ℝ) ^ size (phi m) := pow_le_pow_left₀ (by positivity) hbase_m _
        _ ≤ 1 / 2 := by
          exact pow_le_of_le_one (by norm_num) (by norm_num) (ne_of_gt hNpos)
    have herr : Real.exp ‖X (phi m)‖ *
          (Real.exp (Real.exp (-lambda * size (phi m)) *
            perturbationMajorant (size (phi m)) 1) - 1) < 1 / 2 := by
      calc
        _ ≤ Real.exp ‖X (phi m)‖ *
            (2 * (Real.exp (-lambda * size (phi m)) *
              perturbationMajorant (size (phi m)) 1)) := by
          gcongr
        _ ≤ 2 * size (phi m) * Real.exp (-(lambda / 2) * size (phi m)) := by
          rw [hXnorm]
          calc
            _ ≤ Real.exp (‖y (phi m)‖ * size (phi m)) *
                (2 * (Real.exp (-lambda * size (phi m)) * size (phi m))) := by
              gcongr
            _ = 2 * size (phi m) *
                Real.exp ((‖y (phi m)‖ - lambda) * size (phi m)) := by
              rw [show 2 * (Real.exp (-lambda * size (phi m)) * size (phi m)) =
                (2 * size (phi m)) * Real.exp (-lambda * size (phi m)) by ring]
              have hexpcombine :
                  Real.exp (‖y (phi m)‖ * size (phi m)) *
                    Real.exp (-lambda * size (phi m)) =
                  Real.exp ((‖y (phi m)‖ - lambda) * size (phi m)) := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [show Real.exp (‖y (phi m)‖ * size (phi m)) *
                    (2 * size (phi m) * Real.exp (-lambda * size (phi m))) =
                  (2 * size (phi m)) *
                    (Real.exp (‖y (phi m)‖ * size (phi m)) *
                      Real.exp (-lambda * size (phi m))) by ring,
                hexpcombine]
            _ ≤ 2 * size (phi m) * Real.exp (-(lambda / 2) * size (phi m)) := by
              gcongr
              nlinarith
        _ < 1 / 2 := hdecay_m
    have hlead' : 1 ≤ ‖X (phi m)‖ ^ size (phi m) / (size (phi m)).factorial +
        Real.exp ‖X (phi m)‖ *
          (Real.exp (Real.exp (-lambda * size (phi m)) *
            perturbationMajorant (size (phi m)) 1) - 1) := by
      change 1 ≤ ‖X (phi m)‖ ^ size (phi m) / (size (phi m)).factorial +
        Real.exp ‖X (phi m)‖ *
          (Real.exp (Real.exp (-lambda * size (phi m)) *
            perturbationMajorant (size (phi m)) 1) - 1) at hlead
      exact hlead
    linarith
  have hNnat : Tendsto (fun m ↦ size (phi m)) atTop atTop :=
    hsize.tendsto_atTop.comp hphi.tendsto_atTop
  have hNphi : Tendsto (fun m ↦ (size (phi m) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNnat
  have hnormlim : Tendsto (fun m ↦ ‖y (phi m)‖) atTop (𝓝 ‖c‖) := hylim.norm
  have hepsN : Tendsto (fun m ↦ Real.exp (-lambda * size (phi m)) * size (phi m))
      atTop (𝓝 0) := by
    have hlin : Tendsto (fun m ↦ lambda * (size (phi m) : ℝ)) atTop atTop :=
      hNphi.const_mul_atTop hlambda
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
    have ht' := ht.mul_const lambda⁻¹
    convert ht' using 1 <;> simp [hlambda.ne']
    funext m
    field_simp
  have hepsNle : ∀ᶠ m : ℕ in atTop,
      Real.exp (-lambda * size (phi m)) * size (phi m) ≤ 1 :=
    hepsN.eventually_le_const zero_lt_one
  have hraw : ∀ᶠ m : ℕ in atTop,
      ‖X (phi m)‖ ^ (size (phi m) + 1) / (size (phi m) + 1).factorial ≤
        2 * size (phi m) *
          Real.exp (‖X (phi m)‖ - lambda * size (phi m)) := by
    filter_upwards [hepsNle] with m heps
    have hmaj := perturbationMajorant_one_le (size (phi m))
    have ht0 : 0 ≤ Real.exp (-lambda * size (phi m)) *
        perturbationMajorant (size (phi m)) 1 := by
      apply mul_nonneg (Real.exp_pos _).le
      unfold perturbationMajorant
      positivity
    have ht1 : Real.exp (-lambda * size (phi m)) *
        perturbationMajorant (size (phi m)) 1 ≤ 1 :=
      (mul_le_mul_of_nonneg_left hmaj (Real.exp_pos _).le).trans heps
    have hexpdiff : Real.exp (Real.exp (-lambda * size (phi m)) *
          perturbationMajorant (size (phi m)) 1) - 1 ≤
        2 * (Real.exp (-lambda * size (phi m)) *
          perturbationMajorant (size (phi m)) 1) := by
      have habs := Real.abs_exp_sub_one_le
        (show |Real.exp (-lambda * size (phi m)) *
          perturbationMajorant (size (phi m)) 1| ≤ 1 by
          rw [abs_of_nonneg ht0]
          exact ht1)
      rw [abs_of_nonneg ht0,
        abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht0))] at habs
      exact habs
    have htop := top_coefficient_exponential_bound (z (phi m))
      (show 0 ≤ Real.exp (-lambda * size (phi m)) by positivity) (hsmall (phi m))
    change ‖X (phi m)‖ ^ (size (phi m) + 1) /
        (size (phi m) + 1).factorial ≤
      Real.exp ‖X (phi m)‖ *
        (Real.exp (Real.exp (-lambda * size (phi m)) *
          perturbationMajorant (size (phi m)) 1) - 1) at htop
    calc
      _ ≤ Real.exp ‖X (phi m)‖ *
          (Real.exp (Real.exp (-lambda * size (phi m)) *
            perturbationMajorant (size (phi m)) 1) - 1) := htop
      _ ≤ Real.exp ‖X (phi m)‖ *
          (2 * (Real.exp (-lambda * size (phi m)) *
            perturbationMajorant (size (phi m)) 1)) := by gcongr
      _ ≤ Real.exp ‖X (phi m)‖ *
          (2 * (Real.exp (-lambda * size (phi m)) * size (phi m))) := by gcongr
      _ = 2 * size (phi m) *
          Real.exp (‖X (phi m)‖ - lambda * size (phi m)) := by
        rw [show Real.exp ‖X (phi m)‖ *
              (2 * (Real.exp (-lambda * size (phi m)) * size (phi m))) =
            2 * size (phi m) *
              (Real.exp ‖X (phi m)‖ * Real.exp (-lambda * size (phi m))) by ring,
          ← Real.exp_add]
        congr 2
        ring
  have hleft : Tendsto (fun m ↦
      Real.log (‖X (phi m)‖ ^ (size (phi m) + 1) /
        (size (phi m) + 1).factorial) / size (phi m))
      atTop (𝓝 (1 + Real.log ‖c‖)) := by
    have ht := tendsto_log_scaled_power_div_factorial
      (fun m ↦ size (phi m)) hNnat (fun m ↦ ‖y (phi m)‖) hcpos hnormlim
    apply ht.congr'
    filter_upwards [hNnat.eventually (eventually_ge_atTop 1)] with m hm
    have hnorm : ‖X (phi m)‖ = (size (phi m) : ℝ) * ‖y (phi m)‖ := by
      simp only [y, norm_div, Complex.norm_natCast]
      field_simp
    rw [hnorm]
  have hlog2N : Tendsto (fun m ↦ Real.log (2 * (size (phi m) : ℝ)) /
      size (phi m)) atTop (𝓝 0) := by
    have hlogN : Tendsto (fun m ↦ Real.log (size (phi m) : ℝ) /
        size (phi m)) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hNphi
    have hcst : Tendsto (fun m : ℕ ↦ Real.log 2 / (size (phi m) : ℝ))
        atTop (𝓝 0) :=
      (show Tendsto (fun _ : ℕ ↦ Real.log 2) atTop (𝓝 (Real.log 2)) from
        tendsto_const_nhds).div_atTop hNphi
    simpa only [zero_add] using (hcst.add hlogN).congr' (by
      filter_upwards [hNnat.eventually (eventually_ge_atTop 1)] with m hm
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
      ring)
  have hright : Tendsto (fun m ↦
      Real.log (2 * size (phi m) *
        Real.exp (‖X (phi m)‖ - lambda * size (phi m))) /
          size (phi m)) atTop (𝓝 (‖c‖ - lambda)) := by
    have ht := hlog2N.add (hnormlim.sub_const lambda)
    apply (show Tendsto (fun m ↦ Real.log (2 * (size (phi m) : ℝ)) /
        size (phi m) + (‖y (phi m)‖ - lambda)) atTop
        (𝓝 (‖c‖ - lambda)) by simpa using ht).congr'
    filter_upwards [hNnat.eventually (eventually_ge_atTop 1)] with m hm
    have hnorm : ‖X (phi m)‖ = ‖y (phi m)‖ * size (phi m) := by
      simp only [y, norm_div, Complex.norm_natCast]
      rw [div_mul_cancel₀]
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm))
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, hnorm]
    field_simp
  have hlogineq : ∀ᶠ m : ℕ in atTop,
      Real.log (‖X (phi m)‖ ^ (size (phi m) + 1) /
        (size (phi m) + 1).factorial) / size (phi m) ≤
      Real.log (2 * size (phi m) *
        Real.exp (‖X (phi m)‖ - lambda * size (phi m))) /
          size (phi m) := by
    have hypos : ∀ᶠ m : ℕ in atTop, 0 < ‖y (phi m)‖ :=
      tendsto_const_nhds.eventually_lt hnormlim hcpos
    filter_upwards [hraw, hNnat.eventually (eventually_ge_atTop 1), hypos]
      with m hrawm hm hym
    have hNpos : (0 : ℝ) < size (phi m) := by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hXpos : 0 < ‖X (phi m)‖ := by
      apply norm_pos_iff.mpr
      intro hx
      have hnorm : ‖y (phi m)‖ = ‖X (phi m)‖ / size (phi m) := by simp [y]
      rw [hnorm, hx, norm_zero, zero_div] at hym
      exact (lt_irrefl 0 hym)
    have hlhs : 0 < ‖X (phi m)‖ ^ (size (phi m) + 1) /
        (size (phi m) + 1).factorial := by positivity
    have hrhs : 0 < 2 * size (phi m) *
        Real.exp (‖X (phi m)‖ - lambda * size (phi m)) := by positivity
    exact div_le_div_of_nonneg_right
      (Real.strictMonoOn_log.monotoneOn (by exact hlhs) (by exact hrhs) hrawm)
      hNpos.le
  have hsharp0 : 1 + Real.log ‖c‖ ≤ ‖c‖ - lambda :=
    le_of_tendsto_of_tendsto hleft hright hlogineq
  have hsharp : lambda ≤ ‖c‖ - 1 - Real.log ‖c‖ := by linarith
  have hclt : ‖c‖ < 1 := lt_of_le_of_ne hc_le_one (by
    intro heq
    rw [heq, Real.log_one] at hsharp
    linarith)
  refine ⟨phi, c, hphi, ?_, hcpos, hclt, hsharp⟩
  simpa [y, X] using hylim

end Erdos973
