import Erdos439Power.MajorArcBasics

open scoped BigOperators

namespace Erdos439Power

/-- Variation of a monotone amplitude multiplied by a unit-modulus sequence. -/
lemma weighted_step_variation (w : ℕ → ℝ) (v : ℕ → ℂ) (n : ℕ)
    (hw0 : 0 ≤ w (n + 1)) (hwm : w n ≤ w (n + 1))
    (hv : ‖v n‖ = 1) :
    ‖(w n : ℂ) * v n - (w (n + 1) : ℂ) * v (n + 1)‖ ≤
      w (n + 1) - w n + w (n + 1) * ‖v n - v (n + 1)‖ := by
  have heq : (w n : ℂ) * v n - (w (n + 1) : ℂ) * v (n + 1) =
      ((w n - w (n + 1) : ℝ) : ℂ) * v n +
        (w (n + 1) : ℂ) * (v n - v (n + 1)) := by push_cast; ring
  rw [heq]
  calc
    ‖((w n - w (n + 1) : ℝ) : ℂ) * v n +
        (w (n + 1) : ℂ) * (v n - v (n + 1))‖ ≤
      ‖((w n - w (n + 1) : ℝ) : ℂ) * v n‖ +
        ‖(w (n + 1) : ℂ) * (v n - v (n + 1))‖ := norm_add_le _ _
    _ = w (n + 1) - w n + w (n + 1) * ‖v n - v (n + 1)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hv, mul_one,
        abs_of_nonneg hw0, abs_of_nonpos (sub_nonpos.mpr hwm)]
      ring

/-- Total variation bound, with an actual telescoping position sequence. -/
lemma weighted_total_variation (w P : ℕ → ℝ) (v : ℕ → ℂ)
    (N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ n ≤ N, 0 ≤ w n) (hwm : Monotone w) (hPm : Monotone P)
    (hv : ∀ n ≤ N, ‖v n‖ = 1)
    (hstep : ∀ n < N, ‖v n - v (n + 1)‖ ≤ K * (P (n + 1) - P n)) :
    ‖(w N : ℂ) * v N‖ +
        ∑ n ∈ Finset.range N, ‖(w n : ℂ) * v n - (w (n + 1) : ℂ) * v (n + 1)‖ ≤
      2 * w N + K * w N * (P N - P 0) := by
  have hsum : (∑ n ∈ Finset.range N,
      ‖(w n : ℂ) * v n - (w (n + 1) : ℂ) * v (n + 1)‖) ≤
      ∑ n ∈ Finset.range N,
        (w (n + 1) - w n + K * w N * (P (n + 1) - P n)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnN : n + 1 ≤ N := Finset.mem_range.mp hn
    refine (weighted_step_variation w v n (hw _ hnN)
      (hwm (Nat.le_succ n)) (hv n (by omega))).trans ?_
    apply add_le_add_right
    calc
      w (n + 1) * ‖v n - v (n + 1)‖ ≤
          w (n + 1) * (K * (P (n + 1) - P n)) :=
        mul_le_mul_of_nonneg_left (hstep n (Finset.mem_range.mp hn)) (hw _ hnN)
      _ ≤ w N * (K * (P (n + 1) - P n)) :=
        mul_le_mul_of_nonneg_right (hwm hnN)
          (mul_nonneg hK (sub_nonneg.mpr (hPm (Nat.le_succ n))))
      _ = K * w N * (P (n + 1) - P n) := by ring
  have htel : (∑ n ∈ Finset.range N,
        (w (n + 1) - w n + K * w N * (P (n + 1) - P n))) =
      w N - w 0 + K * w N * (P N - P 0) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_range_sub, Finset.sum_range_sub]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw N le_rfl), hv N le_rfl, mul_one]
  have hwzero := hw 0 (Nat.zero_le N)
  rw [htel] at hsum
  linarith

end Erdos439Power
