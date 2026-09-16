import Erdos439Power.Vendor.ErdosProblems.Erdos439.PowerSums

open scoped BigOperators

namespace Erdos439Power

/-- A zero-mean periodic sequence contributes only its incomplete final period. -/
lemma periodic_sum_remainder (f : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hper : Function.Periodic f q) (hzero : ∑ i ∈ Finset.range q, f i = 0)
    (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range (n % q), f i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < q
      · rw [Nat.mod_eq_of_lt hn]
      · have hqn : q ≤ n := Nat.le_of_not_gt hn
        have hsmall : n - q < n := Nat.sub_lt (hq.trans_le hqn) hq
        have hsplit : n = q + (n - q) := (Nat.add_sub_of_le hqn).symm
        calc
          (∑ i ∈ Finset.range n, f i) =
              (∑ i ∈ Finset.range q, f i) +
                ∑ i ∈ Finset.range (n - q), f (q + i) := by
                  conv_lhs => rw [hsplit]
                  rw [Finset.sum_range_add]
          _ = ∑ i ∈ Finset.range (n - q), f i := by
              rw [hzero, zero_add]
              apply Finset.sum_congr rfl
              intro i _
              simpa only [Nat.add_comm] using hper i
          _ = ∑ i ∈ Finset.range ((n - q) % q), f i := ih _ hsmall
          _ = ∑ i ∈ Finset.range (n % q), f i := by
              have hm : (n - q) % q = n % q := by
                calc
                  (n - q) % q = (q + (n - q)) % q := by simp
                  _ = n % q := by rw [← hsplit]
              rw [hm]

/-- Uniform prefix control for a bounded zero-mean periodic sequence. -/
lemma norm_periodic_prefix_le (f : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hper : Function.Periodic f q) (hzero : ∑ i ∈ Finset.range q, f i = 0)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, f i‖ ≤ C * q := by
  rw [periodic_sum_remainder f q hq hper hzero]
  calc
    ‖∑ i ∈ Finset.range (n % q), f i‖ ≤
        ∑ i ∈ Finset.range (n % q), ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n % q), C := Finset.sum_le_sum (fun i _ => hf i)
    _ = C * ((n % q : ℕ) : ℝ) := by simp [mul_comm]
    _ ≤ C * q := mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt n hq).le) hC

/-- Finite Abel summation bounds a weighted sum by a prefix bound and total variation. -/
lemma norm_weighted_sum_le_variation (w f : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ m ≤ N, ‖∑ j ∈ Finset.range m, f j‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, w n * f n‖ ≤
      B * (‖w N‖ + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖) := by
  rw [Erdos439.PowerDecay.sum_range_mul_eq_boundary_add_differences]
  calc
    ‖w N * (∑ j ∈ Finset.range N, f j) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) *
          (∑ j ∈ Finset.range (n + 1), f j)‖ ≤
      ‖w N * (∑ j ∈ Finset.range N, f j)‖ +
        ∑ n ∈ Finset.range N, ‖(w n - w (n + 1)) *
          (∑ j ∈ Finset.range (n + 1), f j)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ ‖w N‖ * B + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖ * B := by
      simp only [norm_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hf N le_rfl) (norm_nonneg _)
      · apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hf (n + 1) (by simpa using Finset.mem_range.mp hn))
          (norm_nonneg _)
    _ = B * (‖w N‖ + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖) := by
      rw [← Finset.sum_mul]
      ring

end Erdos439Power
