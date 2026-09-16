import Erdos439Power.RealPhase

open scoped BigOperators

namespace Erdos439Power

noncomputable def periodicMean (c : ℕ → ℂ) (q : ℕ) : ℂ :=
  (∑ n ∈ Finset.range q, c n) / (q : ℂ)

lemma norm_periodicMean_le_one (c : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hc : ∀ n, ‖c n‖ ≤ 1) : ‖periodicMean c q‖ ≤ 1 := by
  unfold periodicMean
  rw [norm_div, Complex.norm_natCast, div_le_one (by exact_mod_cast hq)]
  calc
    ‖∑ n ∈ Finset.range q, c n‖ ≤ ∑ n ∈ Finset.range q, ‖c n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range q, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hc n)
    _ = q := by simp

lemma sum_periodic_centered_eq_zero (c : ℕ → ℂ) (q : ℕ) (hq : 0 < q) :
    (∑ n ∈ Finset.range q, (c n - periodicMean c q)) = 0 := by
  rw [Finset.sum_sub_distrib]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, periodicMean]
  field_simp
  ring

/-- Separate the complete rational mean from the bounded periodic residual. -/
theorem norm_periodic_main_term_error_le
    (c : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hper : Function.Periodic c q) (hc : ∀ n, ‖c n‖ ≤ 1)
    (w P : ℕ → ℝ) (N : ℕ) (β : ℝ)
    (hw : ∀ n ≤ N, 0 ≤ w n) (hwm : Monotone w) (hPm : Monotone P) :
    ‖(∑ n ∈ Finset.range N, (w n : ℂ) * realPhase (β * P n) * c n) -
        periodicMean c q * (∑ n ∈ Finset.range N, (w n : ℂ) * realPhase (β * P n))‖ ≤
      (2 * q) * (2 * w N + |β| * w N * (P N - P 0)) := by
  have hrepr : (∑ n ∈ Finset.range N, (w n : ℂ) * realPhase (β * P n) * c n) -
      periodicMean c q * (∑ n ∈ Finset.range N, (w n : ℂ) * realPhase (β * P n)) =
      ∑ n ∈ Finset.range N, (w n : ℂ) * realPhase (β * P n) *
        (c n - periodicMean c q) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hrepr]
  apply norm_periodic_weighted_phase_sum_le _ q hq
    (fun n => by simp only [hper n]) (sum_periodic_centered_eq_zero c q hq)
    2 (by norm_num) _ w P N β hw hwm hPm
  intro n
  exact (norm_sub_le _ _).trans (by
    have := norm_periodicMean_le_one c q hq hc
    have := hc n
    linarith)

end Erdos439Power
