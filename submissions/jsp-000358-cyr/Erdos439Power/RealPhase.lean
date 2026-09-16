import Erdos439Power.WeightedVariation

open scoped BigOperators

namespace Erdos439Power

noncomputable def realPhase (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

@[simp] lemma norm_realPhase (t : ℝ) : ‖realPhase t‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal t

lemma realPhase_add (s t : ℝ) : realPhase (s + t) = realPhase s * realPhase t := by
  simp [realPhase, mul_add, Complex.exp_add]

lemma norm_realPhase_sub_le (s t : ℝ) : ‖realPhase s - realPhase t‖ ≤ |s - t| := by
  have heq : realPhase s - realPhase t = realPhase t * (realPhase (s - t) - 1) := by
    rw [mul_sub, ← realPhase_add]
    simp
  rw [heq, norm_mul, norm_realPhase, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq (Real.norm_eq_abs _)

lemma norm_realPhase_mul_sub_le (β x y : ℝ) (hxy : x ≤ y) :
    ‖realPhase (β * x) - realPhase (β * y)‖ ≤ |β| * (y - x) := by
  have h := norm_realPhase_sub_le (β * x) (β * y)
  rw [← mul_sub, abs_mul, abs_of_nonpos (sub_nonpos.mpr hxy)] at h
  convert h using 1 <;> ring

/-- Finite major-arc error for a zero-mean periodic residual and a monotone mesh. -/
theorem norm_periodic_weighted_phase_sum_le
    (f : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hper : Function.Periodic f q) (hzero : ∑ i ∈ Finset.range q, f i = 0)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C)
    (w P : ℕ → ℝ) (N : ℕ) (β : ℝ)
    (hw : ∀ n ≤ N, 0 ≤ w n) (hwm : Monotone w) (hPm : Monotone P) :
    ‖∑ n ∈ Finset.range N, (w n : ℂ) * realPhase (β * P n) * f n‖ ≤
      (C * q) * (2 * w N + |β| * w N * (P N - P 0)) := by
  refine (norm_weighted_sum_le_variation
    (fun n => (w n : ℂ) * realPhase (β * P n)) f N (C * q)
    (by positivity) (fun m _ => norm_periodic_prefix_le f q hq hper hzero C hC hf m)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact weighted_total_variation w P (fun n => realPhase (β * P n)) N |β|
    (abs_nonneg _) hw hwm hPm (fun _ _ => norm_realPhase _)
    (fun n _ => norm_realPhase_mul_sub_le β _ _ (hPm (Nat.le_succ n)))

end Erdos439Power
