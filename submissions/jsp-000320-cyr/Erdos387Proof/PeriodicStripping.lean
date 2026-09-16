import Mathlib

/-!
# Finite interval stripping of a periodic factor

The argument is the shift-averaging/Cauchy--Schwarz step of BNPZ,
arXiv:2605.21221v2, Lemma 10.2.  Dropping the periodic factor before
expanding the nonnegative square avoids a separate exceptional-unit term.
All statements here concern finite sums, with explicit boundary constants.
-/

namespace Erdos387Proof.PeriodicStripping

open scoped BigOperators ComplexConjugate

noncomputable def intervalSum (A : ℤ) (L : ℕ) (f : ℤ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range L, f (A + (n : ℤ))

theorem intervalSum_shift_sub (A : ℤ) (L t : ℕ) (f : ℤ → ℂ) :
    intervalSum (A + t) L f - intervalSum A L f =
      intervalSum (A + L) t f - intervalSum A t f := by
  have h := Finset.sum_range_add (fun n : ℕ => f (A + n)) L t
  have h' := Finset.sum_range_add (fun n : ℕ => f (A + n)) t L
  rw [Nat.add_comm t L] at h'
  simp only [Nat.cast_add] at h h'
  simp only [intervalSum]
  simp only [add_assoc] at h h' ⊢
  linear_combination h - h'

theorem norm_intervalSum_le (A : ℤ) (L : ℕ) (f : ℤ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) : ‖intervalSum A L f‖ ≤ L := by
  unfold intervalSum
  calc
    ‖∑ n ∈ Finset.range L, f (A + n)‖ ≤
        ∑ n ∈ Finset.range L, ‖f (A + n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range L, (1 : ℝ) := Finset.sum_le_sum fun _ _ => hf _
    _ = L := by simp

theorem norm_intervalSum_shift_sub_le (A : ℤ) (L t : ℕ) (f : ℤ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖intervalSum (A + t) L f - intervalSum A L f‖ ≤ 2 * t := by
  rw [intervalSum_shift_sub]
  exact (norm_sub_le _ _).trans (by
    have h₁ := norm_intervalSum_le (A + L) t f hf
    have h₂ := norm_intervalSum_le A t f hf
    linarith)

private theorem norm_add_sq (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (w * conj z).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Exact square expansion; no norm-one hypothesis is imposed. -/
theorem norm_sum_range_sq_eq (z : ℕ → ℂ) (K : ℕ) :
    ‖∑ k ∈ Finset.range K, z k‖ ^ 2 =
      (∑ k ∈ Finset.range K, ‖z k‖ ^ 2) +
      2 * ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j,
        (z j * conj (z i)).re := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [Finset.sum_range_succ]
    rw [norm_add_sq, ih]
    simp only [map_sum, Finset.mul_sum, Complex.re_sum]
    simp_rw [← Finset.mul_sum]
    ring

/-- Cauchy--Schwarz after discarding a bounded multiplier. -/
theorem norm_sum_mul_sq_le (a b : ℕ → ℂ) (L : ℕ)
    (ha : ∀ n < L, ‖a n‖ ≤ 1) :
    ‖∑ n ∈ Finset.range L, a n * b n‖ ^ 2 ≤
      (L : ℝ) * ∑ n ∈ Finset.range L, ‖b n‖ ^ 2 := by
  have hn : ‖∑ n ∈ Finset.range L, a n * b n‖ ≤
      ∑ n ∈ Finset.range L, ‖b n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ha n (Finset.mem_range.mp hn))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L)
    (fun _ : ℕ => (1 : ℝ)) (fun n => ‖b n‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc

/-- Expand first, sum over the interval, and only then bound correlations. -/
theorem sum_norm_sum_sq_le (f : ℕ → ℕ → ℂ) (L K : ℕ)
    (hf : ∀ n < L, ∀ k < K, ‖f n k‖ ≤ 1) :
    (∑ n ∈ Finset.range L, ‖∑ k ∈ Finset.range K, f n k‖ ^ 2) ≤
      (L : ℝ) * K + 2 * ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j,
        ‖∑ n ∈ Finset.range L, f n j * conj (f n i)‖ := by
  simp_rw [norm_sum_range_sq_eq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hd : (∑ n ∈ Finset.range L, ∑ k ∈ Finset.range K, ‖f n k‖ ^ 2) ≤
      (L : ℝ) * K := by
    calc
      _ ≤ ∑ _n ∈ Finset.range L, ∑ _k ∈ Finset.range K, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro k hk
        have h := hf n (Finset.mem_range.mp hn) k (Finset.mem_range.mp hk)
        nlinarith [norm_nonneg (f n k)]
      _ = _ := by simp
  have hu :
      (∑ n ∈ Finset.range L, ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j,
        (f n j * conj (f n i)).re) ≤
      ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j,
        ‖∑ n ∈ Finset.range L, f n j * conj (f n i)‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    rw [← Complex.re_sum]
    exact Complex.re_le_norm _
  linarith

/-- Boundary error for averaging the shifts `0,s,...,(K-1)s`. -/
theorem norm_average_shift_error_le (A : ℤ) (L K s : ℕ)
    (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖(K : ℂ) * intervalSum A L f -
      ∑ n ∈ Finset.range L, ∑ k ∈ Finset.range K,
        f (A + n + (k*s : ℕ))‖ ≤
      (s : ℝ) * K * (K - 1 : ℕ) := by
  have heq : (K : ℂ) * intervalSum A L f -
      (∑ n ∈ Finset.range L, ∑ k ∈ Finset.range K,
        f (A + n + (k*s : ℕ))) =
      ∑ k ∈ Finset.range K,
        (intervalSum A L f - intervalSum (A + (k*s : ℕ)) L f) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    congr 1
    unfold intervalSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    omega
  rw [heq]
  calc
    _ ≤ ∑ k ∈ Finset.range K,
        ‖intervalSum A L f - intervalSum (A + (k*s : ℕ)) L f‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range K, (2 : ℝ) * (k*s : ℕ) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_sub_rev]
      exact norm_intervalSum_shift_sub_le A L (k*s) f hf
    _ = (s : ℝ) * K * (K - 1 : ℕ) := by
      have h := Finset.sum_range_id_mul_two K
      have hr : (∑ k ∈ Finset.range K, (k : ℝ)) * 2 =
          (K : ℝ) * (K - 1 : ℕ) := by
        simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using
          congrArg (fun x : ℕ => (x : ℝ)) h
      simp only [Nat.cast_mul]
      simp_rw [show ∀ k : ℕ, (2 : ℝ) * (k * s) = (k : ℝ) * (2*s) by intro; ring]
      rw [← Finset.sum_mul]
      nlinarith


noncomputable def correlationMass (A : ℤ) (L K s : ℕ) (b : ℤ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j,
    ‖intervalSum A L (fun n => b (n + (j*s : ℕ)) * conj (b (n + (i*s : ℕ))))‖

/-- The division-free conductor-stripping inequality, including zero-length
intervals, zero step, and zero averaging length. -/
theorem interval_periodic_factor_sq_mul_le
    (A : ℤ) (L K s : ℕ) (a b : ℤ → ℂ)
    (ha : Function.Periodic a (s : ℤ))
    (ha_norm : ∀ n, ‖a n‖ ≤ 1) (hb_norm : ∀ n, ‖b n‖ ≤ 1) :
    (K : ℝ)^2 * ‖intervalSum A L (fun n => a n * b n)‖^2 ≤
      2 * (L : ℝ)^2 * K + 4 * L * correlationMass A L K s b +
      2 * (s : ℝ)^2 * K^2 * (K - 1 : ℕ)^2 := by
  let z : ℤ → ℂ := fun n => a n * b n
  let T : ℂ := ∑ n ∈ Finset.range L, ∑ k ∈ Finset.range K,
    z (A + n + (k*s : ℕ))
  let U : ℕ → ℂ := fun n => ∑ k ∈ Finset.range K,
    b (A + n + (k*s : ℕ))
  have hz : ∀ n, ‖z n‖ ≤ 1 := by
    intro n
    dsimp [z]
    rw [norm_mul]
    exact (mul_le_mul (ha_norm n) (hb_norm n) (norm_nonneg _) (by positivity)).trans
      (by norm_num)
  have hT : T = ∑ n ∈ Finset.range L, a (A + n) * U n := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [U]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [z]
    rw [ha.nat_mul k (A + n)]
  have hcs : ‖T‖^2 ≤ (L : ℝ) * ∑ n ∈ Finset.range L, ‖U n‖^2 := by
    rw [hT]
    exact norm_sum_mul_sq_le (fun n => a (A + n)) U L (fun n _ => ha_norm _)
  have he : (∑ n ∈ Finset.range L, ‖U n‖^2) ≤
      (L : ℝ)*K + 2*correlationMass A L K s b := by
    exact sum_norm_sum_sq_le
      (fun n k => b (A + n + (k*s : ℕ))) L K (fun n _ k _ => hb_norm _)
  have hbound : ‖T‖^2 ≤ (L : ℝ)^2*K + 2*L*correlationMass A L K s b := by
    have := hcs.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg L))
    nlinarith
  have herr := norm_average_shift_error_le A L K s z hz
  change ‖(K : ℂ) * intervalSum A L z - T‖ ≤ _ at herr
  have htri : (K : ℝ) * ‖intervalSum A L z‖ ≤
      ‖T‖ + (s : ℝ)*K*(K-1 : ℕ) := by
    have hh := norm_add_le ((K : ℂ) * intervalSum A L z - T) T
    rw [sub_add_cancel, norm_mul, Complex.norm_natCast] at hh
    linarith
  have hsq : ((K : ℝ) * ‖intervalSum A L z‖)^2 ≤
      (‖T‖ + (s : ℝ)*K*(K-1 : ℕ))^2 := by
    exact pow_le_pow_left₀ (by positivity) htri 2
  have hsplit : (‖T‖ + (s : ℝ)*K*(K-1 : ℕ))^2 ≤
      2*‖T‖^2 + 2*((s : ℝ)*K*(K-1 : ℕ))^2 := by
    nlinarith [sq_nonneg (‖T‖ - (s : ℝ)*K*(K-1 : ℕ))]
  change (K : ℝ)^2 * ‖intervalSum A L z‖^2 ≤ _
  nlinarith

/-- Explicit finite conductor stripping, with a positive averaging length. -/
theorem interval_periodic_factor_sq_le
    (A : ℤ) (L K s : ℕ) (hK : 0 < K) (a b : ℤ → ℂ)
    (ha : Function.Periodic a (s : ℤ))
    (ha_norm : ∀ n, ‖a n‖ ≤ 1) (hb_norm : ∀ n, ‖b n‖ ≤ 1) :
    ‖intervalSum A L (fun n => a n * b n)‖^2 ≤
      2 * (L : ℝ)^2 / K +
      (4 * L / (K : ℝ)^2) * correlationMass A L K s b +
      2 * (s : ℝ)^2 * ((K : ℝ)-1)^2 := by
  have h := interval_periodic_factor_sq_mul_le A L K s a b ha ha_norm hb_norm
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have he : ((K-1 : ℕ) : ℝ) = (K : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K)]
    norm_num
  rw [he] at h
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hk)).mp
  convert h using 1
  all_goals try field_simp [ne_of_gt hk]
  rfl

end Erdos387Proof.PeriodicStripping
