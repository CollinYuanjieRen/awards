import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Uniform tails of the truncated complex exponential

This is the exact analytic statement of Luo--Yang--Zhu Lemma 3.1.  It is
scaffolded independently of the power-sum argument so its Stirling/geometric
tail proof can be compiled and audited in isolation.
-/

open Finset

namespace Erdos973

private theorem norm_exp_sub_sum_le_geometric
    {x : ℂ} {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx : ‖x‖ / n.succ ≤ q) :
    ‖Complex.exp x - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤
      ‖x‖ ^ n / n.factorial * (1 - q)⁻¹ := by
  rw [← CauSeq.lim_const (abv := norm) (∑ m ∈ range n, _), Complex.exp,
    sub_eq_add_neg, ← CauSeq.lim_neg, CauSeq.lim_add, ← Complex.lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj ↦ ?_⟩)
  simp_rw [← sub_eq_add_neg]
  change ‖(∑ m ∈ range j, x ^ m / m.factorial) -
      ∑ m ∈ range n, x ^ m / m.factorial‖ ≤ _
  let k := j - n
  have hj' : j = n + k := (Nat.add_sub_of_le hj).symm
  rw [hj', sum_range_add_sub_sum_range]
  calc
    ‖∑ i ∈ range k, x ^ (n + i) / ((n + i).factorial : ℂ)‖ ≤
        ∑ i ∈ range k, ‖x ^ (n + i) / ((n + i).factorial : ℂ)‖ :=
      IsAbsoluteValue.abv_sum _ _ _
    _ ≤ ∑ i ∈ range k, ‖x‖ ^ (n + i) / (n + i).factorial := by
      simp
    _ ≤ ∑ i ∈ range k,
        ‖x‖ ^ (n + i) / ((n.factorial : ℝ) * (n.succ : ℝ) ^ i) := by
      gcongr
      exact_mod_cast Nat.factorial_mul_pow_le_factorial
    _ = ∑ i ∈ range k, ‖x‖ ^ n / n.factorial * (‖x‖ / (n.succ : ℝ)) ^ i := by
      congr 1
      funext i
      rw [pow_add, div_pow]
      field_simp
    _ ≤ ‖x‖ ^ n / n.factorial * ∑ i ∈ range k, q ^ i := by
      rw [← mul_sum]
      gcongr
    _ ≤ ‖x‖ ^ n / n.factorial * (1 - q)⁻¹ := by
      gcongr
      rw [← tsum_geometric_of_lt_one hq0 hq1]
      exact (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun i _ ↦ pow_nonneg hq0 i)

private theorem pow_div_factorial_le_exp_rate
    {Q : ℝ} (hQ0 : 0 < Q) {n : ℕ} (hn : 0 < n) :
    (Q * n) ^ n / n.factorial ≤ Real.exp ((1 + Real.log Q) * n) := by
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
    (Q * n) ^ n / n.factorial
        ≤ (Q * n) ^ n / ((n : ℝ) / Real.exp 1) ^ n := by
          exact div_le_div_of_nonneg_left (pow_nonneg (mul_nonneg hQ0.le hnR.le) n)
            (pow_pos (by positivity) n) hfac
    _ = (Q * Real.exp 1) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp
    _ = Real.exp ((1 + Real.log Q) * n) := by
      rw [show Q * Real.exp 1 = Real.exp (1 + Real.log Q) by
        rw [Real.exp_add, Real.exp_log hQ0]
        ring]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private theorem next_pow_div_factorial_le
    {t q : ℝ} {n : ℕ} (ht : 0 ≤ t) (hq : q ≤ 1)
    (h : t / n.succ ≤ q) :
    t ^ (n + 1) / (n + 1).factorial ≤ t ^ n / n.factorial := by
  calc
    t ^ (n + 1) / (n + 1).factorial
        = (t ^ n / n.factorial) * (t / n.succ) := by
          rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
          field_simp
    _ ≤ (t ^ n / n.factorial) * q := by gcongr
    _ ≤ (t ^ n / n.factorial) * 1 := by gcongr
    _ = _ := by ring

/-- `E_m(u) = sum_{j=0}^m u^j/j!`. -/
noncomputable def truncatedExp (m : ℕ) (u : ℂ) : ℂ :=
  ∑ j ∈ range (m + 1), u ^ j / (j.factorial : ℂ)

/-- The paper's convention `E_{-1} = 0`, expressed without integer indices. -/
noncomputable def truncatedExpPred (n : ℕ) (u : ℂ) : ℂ :=
  match n with
  | 0 => 0
  | m + 1 => truncatedExp m u

/-- Luo--Yang--Zhu Lemma 3.1: below every fixed linear radius `Q n`, both
relevant exponential tails have rate at most `1 + log Q + eta`. -/
theorem exponential_tail_bound
    {Q eta : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ u : ℂ, ‖u‖ ≤ Q * n →
      ‖Complex.exp u - truncatedExp n u‖ +
          ‖Complex.exp u - truncatedExpPred n u‖ ≤
        Real.exp ((1 + Real.log Q + eta) * n) := by
  have hgeom : 0 ≤ (1 - Q)⁻¹ := by positivity
  have htendsto : Filter.Tendsto
      (fun n : ℕ ↦ Real.exp (eta * n)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop heta)
  have heventually : ∀ᶠ n : ℕ in Filter.atTop,
      2 * (1 - Q)⁻¹ ≤ Real.exp (eta * n) :=
    htendsto.eventually (Filter.eventually_ge_atTop (2 * (1 - Q)⁻¹))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨max 1 N₀, fun n hnN u hu ↦ ?_⟩
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left 1 N₀) hnN)
  have hN₀n : N₀ ≤ n := le_trans (le_max_right 1 N₀) hnN
  have hratio : ‖u‖ / n.succ ≤ Q := by
    rw [div_le_iff₀ (by positivity)]
    calc
      ‖u‖ ≤ Q * n := hu
      _ ≤ Q * n.succ := by
        gcongr
        exact Nat.le_succ n
  have hratio' : ‖u‖ / n.succ.succ ≤ Q := by
    rw [div_le_iff₀ (by positivity)]
    calc
      ‖u‖ ≤ Q * n := hu
      _ ≤ Q * n.succ.succ := by
        gcongr
        exact le_trans (Nat.le_succ n) (Nat.le_succ n.succ)
  have htailPred :
      ‖Complex.exp u - truncatedExpPred n u‖ ≤
        ‖u‖ ^ n / n.factorial * (1 - Q)⁻¹ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa [truncatedExpPred, truncatedExp] using
      (norm_exp_sub_sum_le_geometric (x := u) (n := k + 1)
        hQ0.le hQ1 hratio)
  have htail :
      ‖Complex.exp u - truncatedExp n u‖ ≤
        ‖u‖ ^ (n + 1) / (n + 1).factorial * (1 - Q)⁻¹ := by
    simpa [truncatedExp, Nat.add_assoc] using
      (norm_exp_sub_sum_le_geometric (x := u) (n := n + 1)
        hQ0.le hQ1 hratio')
  have hnext :
      ‖u‖ ^ (n + 1) / (n + 1).factorial ≤ ‖u‖ ^ n / n.factorial :=
    next_pow_div_factorial_le (norm_nonneg u) hQ1.le hratio
  have hterm :
      ‖u‖ ^ n / n.factorial ≤ Real.exp ((1 + Real.log Q) * n) := by
    calc
      ‖u‖ ^ n / n.factorial ≤ (Q * n) ^ n / n.factorial := by gcongr
      _ ≤ Real.exp ((1 + Real.log Q) * n) :=
        pow_div_factorial_le_exp_rate hQ0 hn
  calc
    ‖Complex.exp u - truncatedExp n u‖ +
          ‖Complex.exp u - truncatedExpPred n u‖
        ≤ (‖u‖ ^ n / n.factorial * (1 - Q)⁻¹) +
            (‖u‖ ^ n / n.factorial * (1 - Q)⁻¹) := by
              gcongr
              exact htail.trans (mul_le_mul_of_nonneg_right hnext hgeom)
    _ = 2 * (‖u‖ ^ n / n.factorial * (1 - Q)⁻¹) := by ring
    _ ≤ 2 * (Real.exp ((1 + Real.log Q) * n) * (1 - Q)⁻¹) := by
      gcongr
    _ = Real.exp ((1 + Real.log Q) * n) * (2 * (1 - Q)⁻¹) := by ring
    _ ≤ Real.exp ((1 + Real.log Q) * n) * Real.exp (eta * n) := by
      gcongr
      exact hN₀ n hN₀n
    _ = Real.exp ((1 + Real.log Q + eta) * n) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Erdos973
