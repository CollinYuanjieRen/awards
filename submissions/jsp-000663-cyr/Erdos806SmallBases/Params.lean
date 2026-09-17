import Erdos806SmallBases.Assembly

/-! Choice of parameters: the `ε`-`N` form of the theorem. -/

namespace Erdos806

theorem exists_pow_between (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    ∃ q, 0 < q ∧ m ≤ q ^ k ∧ q ^ k ≤ 2 ^ k * m := by
  have hex : ∃ q, m ≤ q ^ k := ⟨m, Nat.le_self_pow (by omega) m⟩
  have hq : m ≤ (Nat.find hex) ^ k := Nat.find_spec hex
  set q := Nat.find hex with hqdef
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, zero_pow (by omega : k ≠ 0)] at hq; omega
    · exact h
  refine ⟨q, hq0, hq, ?_⟩
  by_cases h1 : q = 1
  · rw [h1, one_pow]
    have h2 : 0 < 2 ^ k * m := Nat.mul_pos (pow_pos (by norm_num) k) hm
    omega
  · have h2 : 2 ≤ q := by omega
    have hmin : ¬ (m ≤ (q - 1) ^ k) := Nat.find_min hex (by omega)
    have hlt : (q - 1) ^ k < m := not_le.mp hmin
    have hle : q ≤ 2 * (q - 1) := by omega
    calc q ^ k ≤ (2 * (q - 1)) ^ k := Nat.pow_le_pow_left hle k
      _ = 2 ^ k * (q - 1) ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * m := Nat.mul_le_mul le_rfl (le_of_lt hlt)

theorem erdos_806_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ Real.sqrt n →
      ∃ B : Finset ℤ, HasBasis A B ∧ (B.card : ℝ) ≤ ε * Real.sqrt n := by
  -- choose `k` with `4 ≤ ε * k`
  obtain ⟨k, hk, hk4⟩ : ∃ k : ℕ, 0 < k ∧ (4 : ℝ) ≤ ε * (k : ℝ) := by
    refine ⟨⌈(4 : ℝ) / ε⌉₊ + 1, by omega, ?_⟩
    have h1 : (4 : ℝ) / ε ≤ (⌈(4 : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hε] at h1
    push_cast
    nlinarith [hε]
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- choose `C` with `2^(k+4) * k^2 ≤ ε * C`
  obtain ⟨C, hC1, hCbound⟩ : ∃ C : ℕ, 1 ≤ C ∧ (2 : ℝ) ^ (k + 4) * (k : ℝ) ^ 2 ≤ ε * (C : ℝ) := by
    refine ⟨⌈(2 : ℝ) ^ (k + 4) * (k : ℝ) ^ 2 / ε⌉₊ + 1, by omega, ?_⟩
    have h1 : (2 : ℝ) ^ (k + 4) * (k : ℝ) ^ 2 / ε ≤ (⌈(2 : ℝ) ^ (k + 4) * (k : ℝ) ^ 2 / ε⌉₊ : ℝ) :=
      Nat.le_ceil _
    rw [div_le_iff₀ hε] at h1
    push_cast
    nlinarith [hε]
  have hCR : (0 : ℝ) < (C : ℝ) := by
    have : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
    linarith
  -- choose `M` so that `n ≥ M` forces `(4/ε)^2 ≤ n`
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ((4 : ℝ) / ε) ^ 2 ≤ (n : ℝ) := by
    refine ⟨⌈((4 : ℝ) / ε) ^ 2⌉₊, fun n hn => ?_⟩
    have h1 : ((4 : ℝ) / ε) ^ 2 ≤ (⌈((4 : ℝ) / ε) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈((4 : ℝ) / ε) ^ 2⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine ⟨max (max (C ^ (2 * k)) M) 1, ?_⟩
  intro n hn A hA hcard
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  have hs0 : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hss : s * s = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hs1 : (1 : ℝ) ≤ s := by nlinarith
  set r : ℕ := ⌊s⌋₊ with hrdef
  have hr1 : (r : ℝ) ≤ s := Nat.floor_le hs0
  have hr2 : s < (r : ℝ) + 1 := Nat.lt_floor_add_one s
  obtain ⟨q, hq0, hq1, hq2⟩ :=
    exists_pow_between k (k * (r + 1)) hk (Nat.mul_pos hk (by omega))
  obtain ⟨B, hB, hcardB⟩ := exists_basis_bound q k n hq0 hk A hA
  refine ⟨B, hB, ?_⟩
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hqkR : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hqR k
  have hq1R : (k : ℝ) * ((r : ℝ) + 1) ≤ (q : ℝ) ^ k := by exact_mod_cast hq1
  have hq2R : (q : ℝ) ^ k ≤ 2 ^ k * ((k : ℝ) * ((r : ℝ) + 1)) := by exact_mod_cast hq2
  -- cast the combinatorial bound
  have hBR : (B.card : ℝ) ≤ 2 * (k : ℝ) * (q : ℝ) ^ (k - 1) + ((A.card / k : ℕ) : ℝ)
      + ((n / q ^ k : ℕ) : ℝ) + 1 := by
    have h : ((B.card : ℕ) : ℝ)
        ≤ ((2 * k * q ^ (k - 1) + A.card / k + n / q ^ k + 1 : ℕ) : ℝ) := by exact_mod_cast hcardB
    push_cast at h
    linarith
  -- (i) the `A.card / k` term
  have t1 : ((A.card / k : ℕ) : ℝ) ≤ ε / 4 * s := by
    have h1 : ((A.card / k : ℕ) : ℝ) ≤ (A.card : ℝ) / (k : ℝ) := Nat.cast_div_le
    have h2 : (A.card : ℝ) / (k : ℝ) ≤ s / (k : ℝ) := by gcongr
    have h3 : s / (k : ℝ) ≤ ε / 4 * s := by
      rw [div_le_iff₀ hkR]
      nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ ε * (k : ℝ) - 4)]
    linarith
  -- (ii) the `n / q^k` term
  have t2 : ((n / q ^ k : ℕ) : ℝ) ≤ ε / 4 * s := by
    have h1 : ((n / q ^ k : ℕ) : ℝ) ≤ (n : ℝ) / ((q : ℝ) ^ k) := by
      calc ((n / q ^ k : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) / ((q ^ k : ℕ) : ℝ) := Nat.cast_div_le
        _ = (n : ℝ) / ((q : ℝ) ^ k) := by push_cast; ring
    have hks : (k : ℝ) * s ≤ (q : ℝ) ^ k := by
      nlinarith [mul_nonneg (le_of_lt hkR) (by linarith : (0 : ℝ) ≤ (r : ℝ) + 1 - s)]
    have h2 : (n : ℝ) / ((q : ℝ) ^ k) ≤ ε / 4 * s := by
      rw [div_le_iff₀ hqkR]
      have hstep : ε / 4 * s * ((k : ℝ) * s) ≤ ε / 4 * s * ((q : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hks (by positivity)
      have he : ε / 4 * s * ((k : ℝ) * s) = ε * (k : ℝ) * (s * s) / 4 := by ring
      rw [hss] at he
      nlinarith [hstep, he,
        mul_nonneg (by linarith : (0 : ℝ) ≤ ε * (k : ℝ) - 4) (by linarith : (0 : ℝ) ≤ (n : ℝ))]
    linarith
  -- `C ≤ q`
  have hCk : (C : ℝ) ^ k ≤ s := by
    have hnge : C ^ (2 * k) ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnge' : ((C : ℝ)) ^ (2 * k) ≤ (n : ℝ) := by exact_mod_cast hnge
    have hpow : ((C : ℝ) ^ k) ^ 2 = (C : ℝ) ^ (2 * k) := by rw [← pow_mul, mul_comm]
    have hle : Real.sqrt (((C : ℝ) ^ k) ^ 2) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by rw [hpow]; exact hnge')
    rwa [Real.sqrt_sq (by positivity)] at hle
  have hCkq : C ^ k < q ^ k := by
    have hA1 : ((C ^ k : ℕ) : ℝ) < (r : ℝ) + 1 := by
      have he : ((C ^ k : ℕ) : ℝ) = (C : ℝ) ^ k := by push_cast; ring
      rw [he]; linarith
    have hA2 : C ^ k < r + 1 := by exact_mod_cast hA1
    have hA3 : r + 1 ≤ k * (r + 1) := Nat.le_mul_of_pos_left _ hk
    exact lt_of_lt_of_le hA2 (le_trans hA3 hq1)
  have hCleq : C ≤ q := by
    by_contra hcon
    exact absurd (Nat.pow_lt_pow_left (by omega : q < C) (by omega : k ≠ 0))
      (not_lt.mpr (le_of_lt hCkq))
  have hCleqR : (C : ℝ) ≤ (q : ℝ) := by exact_mod_cast hCleq
  -- (iii) the main `2 * k * q^(k-1)` term
  have t3 : 2 * (k : ℝ) * (q : ℝ) ^ (k - 1) ≤ ε / 4 * s := by
    have hpq : (q : ℝ) ^ (k - 1) * (q : ℝ) = (q : ℝ) ^ k := by
      rw [← pow_succ]; congr 1; omega
    have hnn : (0 : ℝ) ≤ 2 * (k : ℝ) * (q : ℝ) ^ (k - 1) := by positivity
    have hmain : 2 * (k : ℝ) * (q : ℝ) ^ (k - 1) * (q : ℝ) ≤ 2 ^ (k + 2) * (k : ℝ) ^ 2 * s := by
      have e1 : 2 * (k : ℝ) * (q : ℝ) ^ (k - 1) * (q : ℝ) = 2 * (k : ℝ) * ((q : ℝ) ^ k) := by
        rw [← hpq]; ring
      rw [e1]
      calc 2 * (k : ℝ) * ((q : ℝ) ^ k)
          ≤ 2 * (k : ℝ) * (2 ^ k * ((k : ℝ) * ((r : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hq2R (by positivity)
        _ ≤ 2 * (k : ℝ) * (2 ^ k * ((k : ℝ) * (2 * s))) := by
            gcongr
            linarith
        _ = 2 ^ (k + 2) * (k : ℝ) ^ 2 * s := by ring
    have hstep : 2 * (k : ℝ) * (q : ℝ) ^ (k - 1) * (C : ℝ) ≤ 2 ^ (k + 2) * (k : ℝ) ^ 2 * s :=
      le_trans (mul_le_mul_of_nonneg_left hCleqR hnn) hmain
    have hfin : 2 ^ (k + 2) * (k : ℝ) ^ 2 * s ≤ ε / 4 * s * (C : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hCbound hs0
      have hpow2 : (2 : ℝ) ^ (k + 4) = 4 * 2 ^ (k + 2) := by ring
      rw [hpow2] at h
      linarith
    exact le_of_mul_le_mul_right (le_trans hstep hfin) hCR
  -- (iv) the `+1`
  have t4 : (1 : ℝ) ≤ ε / 4 * s := by
    have h3 : ((4 : ℝ) / ε) ^ 2 ≤ (n : ℝ) :=
      hM n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
    have h4 : (4 : ℝ) / ε ≤ s := by
      have h5 : Real.sqrt (((4 : ℝ) / ε) ^ 2) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h3
      rwa [Real.sqrt_sq (by positivity)] at h5
    rw [div_le_iff₀ hε] at h4
    nlinarith [h4]
  linarith [hBR, t1, t2, t3, t4]


end Erdos806
