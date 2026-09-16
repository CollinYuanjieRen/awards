import Erdos439Power.Vendor.ErdosProblems.Erdos439.PowerSums

open scoped BigOperators

namespace Erdos439

private lemma nat_mul_pow_gap_le (N j : ℕ) (hN : 1 ≤ N) :
    N * ((N + 1) ^ j - N ^ j) ≤ 2 ^ j * N ^ j := by
  have hexpand :
      (N + 1) ^ j - N ^ j =
        ∑ i ∈ Finset.range j, j.choose i * N ^ i := by
    rw [add_pow, Finset.sum_range_succ]
    simp [Nat.choose_self, mul_comm]
  rw [hexpand, Finset.mul_sum]
  calc
    ∑ i ∈ Finset.range j, N * (j.choose i * N ^ i)
        ≤ ∑ i ∈ Finset.range j, j.choose i * N ^ j := by
          apply Finset.sum_le_sum
          intro i hi
          have hij : i + 1 ≤ j := Finset.mem_range.mp hi
          have hp : N ^ (i + 1) ≤ N ^ j :=
            Nat.pow_le_pow_right hN hij
          calc
            N * (j.choose i * N ^ i) = j.choose i * N ^ (i + 1) := by
              simp [pow_succ, mul_comm, mul_assoc]
            _ ≤ j.choose i * N ^ j := Nat.mul_le_mul_left _ hp
    _ ≤ ∑ i ∈ Finset.range (j + 1), j.choose i * N ^ j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_succ j)) (by intros; positivity)
    _ = 2 ^ j * N ^ j := by
      rw [← Finset.sum_mul, Nat.sum_range_choose]

private lemma real_mul_pow_gap_le (N j : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * ((((N + 1 : ℕ) : ℝ) ^ j) - (N : ℝ) ^ j) ≤
      (2 : ℝ) ^ j * (N : ℝ) ^ j := by
  simp only [← Nat.cast_pow]
  rw [← Nat.cast_sub (Nat.pow_le_pow_left N.le_succ j)]
  exact_mod_cast nat_mul_pow_gap_le N j hN

/-- The last mesh interval of the normalized power polynomial is uniformly
controlled by its endpoint value. -/
theorem mul_normalizedPowerGap_le (k L N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    (N : ℝ) * normalizedPowerGap k L N ≤
      (2 ^ k : ℝ) * normalizedPower k L N := by
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc
      (1 : ℝ) ≤ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hterm : ∀ j ∈ Finset.Icc 2 k,
      (N : ℝ) *
          ((k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) : ℝ) *
            ((((N + 1 : ℕ) : ℝ) ^ j) - (N : ℝ) ^ j)) ≤
        (2 : ℝ) ^ k *
          ((k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) : ℝ) * (N : ℝ) ^ j) := by
    intro j hj
    have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
    have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) hjk
    have hgap := real_mul_pow_gap_le N j hN
    have hc : 0 ≤
        (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
          L ^ (j - 1) : ℝ) := by positivity
    calc
      (N : ℝ) *
          ((k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) : ℝ) *
            ((((N + 1 : ℕ) : ℝ) ^ j) - (N : ℝ) ^ j)) =
          (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) : ℝ) *
            ((N : ℝ) * ((((N + 1 : ℕ) : ℝ) ^ j) - (N : ℝ) ^ j)) := by ring
      _ ≤ (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) : ℝ) * ((2 : ℝ) ^ j * (N : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hgap hc
      _ ≤ (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) : ℝ) * ((2 : ℝ) ^ k * (N : ℝ) ^ j) := by
        gcongr
      _ = (2 : ℝ) ^ k *
          ((k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) : ℝ) * (N : ℝ) ^ j) := by ring
  have hgaprepr : normalizedPowerGap k L N =
      1 + ∑ j ∈ Finset.Icc 2 k,
        (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
          L ^ (j - 1) : ℝ) *
          ((((N + 1 : ℕ) : ℝ) ^ j) - (N : ℝ) ^ j) := by
    unfold normalizedPowerGap normalizedPower
    push_cast
    calc
      ((N : ℝ) + 1 + ∑ j ∈ Finset.Icc 2 k,
          (k.choose j : ℝ) * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) * ((N : ℝ) + 1) ^ j) -
          ((N : ℝ) + ∑ j ∈ Finset.Icc 2 k,
            (k.choose j : ℝ) * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) * (N : ℝ) ^ j) =
        1 + ((∑ j ∈ Finset.Icc 2 k,
          (k.choose j : ℝ) * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) * ((N : ℝ) + 1) ^ j) -
          ∑ j ∈ Finset.Icc 2 k,
            (k.choose j : ℝ) * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) * (N : ℝ) ^ j) := by ring
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply congrArg (fun x : ℝ ↦ 1 + x)
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hpowerrepr : (normalizedPower k L N : ℝ) =
      (N : ℝ) + ∑ j ∈ Finset.Icc 2 k,
        (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
          L ^ (j - 1) : ℝ) * (N : ℝ) ^ j := by
    simp only [normalizedPower, Nat.cast_add, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_pow]
    norm_num
  rw [hgaprepr, hpowerrepr]
  calc
    (N : ℝ) * (1 + ∑ j ∈ Finset.Icc 2 k,
        (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
          L ^ (j - 1) : ℝ) *
          ((((N + 1 : ℕ) : ℝ) ^ j) - (N : ℝ) ^ j)) =
      (N : ℝ) + ∑ j ∈ Finset.Icc 2 k,
        (N : ℝ) *
          ((k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) : ℝ) *
            ((((N + 1 : ℕ) : ℝ) ^ j) - (N : ℝ) ^ j)) := by
      rw [mul_add, mul_one, Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ k * (N : ℝ) +
        ∑ j ∈ Finset.Icc 2 k, (2 : ℝ) ^ k *
          ((k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) : ℝ) * (N : ℝ) ^ j) := by
      exact add_le_add
        (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg N))
        (Finset.sum_le_sum hterm)
    _ = (2 : ℝ) ^ k *
        ((N : ℝ) + ∑ j ∈ Finset.Icc 2 k,
          (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) : ℝ) * (N : ℝ) ^ j) := by
      rw [mul_add, Finset.mul_sum]

end Erdos439
