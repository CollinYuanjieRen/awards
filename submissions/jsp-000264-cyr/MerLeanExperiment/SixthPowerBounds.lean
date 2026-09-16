import Mathlib

namespace ReciprocalSquares

/-- A reciprocal sixth power is bounded by a fifth-power telescoping difference. -/
private theorem recip_sixth_le_telescope (x : ℝ) (hx : 2 ≤ x) :
    1 / x ^ 6 ≤ 1 / (x - 1) ^ 5 - 1 / x ^ 5 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  rw [le_sub_iff_add_le]
  have hid : 1 / x ^ 6 + 1 / x ^ 5 = (1 + x) / x ^ 6 := by
    field_simp
  rw [hid]
  apply (div_le_div_iff₀ (pow_pos hx0 6) (pow_pos hx1 5)).2
  calc
    (1 + x) * (x - 1) ^ 5 = ((x + 1) * (x - 1)) * (x - 1) ^ 4 := by ring
    _ ≤ x ^ 2 * x ^ 4 := by
      apply mul_le_mul
      · nlinarith
      · exact pow_le_pow_left₀ hx1.le (by linarith) 4
      · positivity
      · positivity
    _ = x ^ 6 := by ring
    _ = 1 * x ^ 6 := by ring

/-- A finite real reciprocal-sixth-power tail is bounded by its first
fifth-power telescoping term. -/
theorem finite_sixth_tail
    (s : Finset ℕ) (K : ℕ) (hK : 2 ≤ K)
    (hs : ∀ n ∈ s, K ≤ n) :
    ∑ n ∈ s, (1 : ℝ) / (n : ℝ)^6 ≤
      1 / ((K : ℝ) - 1)^5 := by
  by_cases hsempty : s = ∅
  · have hKreal : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
    simp [hsempty]
    positivity
  have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsempty
  let M := s.sup id
  have hKM : K ≤ M := by
    calc
      K ≤ hsne.choose := hs hsne.choose hsne.choose_spec
      _ ≤ s.sup id := Finset.le_sup (f := id) hsne.choose_spec
      _ = M := rfl
  have hsub : s ⊆ Finset.Icc K M := by
    intro n hn
    have hnM : n ≤ M := by
      simpa [M] using Finset.le_sup (f := id) hn
    exact Finset.mem_Icc.mpr ⟨hs n hn, hnM⟩
  have henlarge :
      (∑ n ∈ s, (1 : ℝ) / (n : ℝ)^6) ≤
        ∑ n ∈ Finset.Icc K M, (1 : ℝ) / (n : ℝ)^6 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn _
    have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < K) (Finset.mem_Icc.mp hn).1)
    positivity
  have hsixth :
      (∑ n ∈ Finset.Icc K M, (1 : ℝ) / (n : ℝ)^6) ≤
        ∑ n ∈ Finset.Icc K M,
          (1 / ((n : ℝ) - 1)^5 - 1 / (n : ℝ)^5) := by
    apply Finset.sum_le_sum
    intro n hn
    apply recip_sixth_le_telescope
    exact_mod_cast hK.trans (Finset.mem_Icc.mp hn).1
  have htel : ∀ L : ℕ, K ≤ L →
      (∑ n ∈ Finset.Icc K L,
        (1 / ((n : ℝ) - 1)^5 - 1 / (n : ℝ)^5)) =
        1 / ((K : ℝ) - 1)^5 - 1 / (L : ℝ)^5 := by
    intro L hKL
    induction L, hKL using Nat.le_induction with
    | base => simp
    | succ L hKL ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hKL), ih]
      push_cast
      ring
  have hM0 : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < K) hKM)
  calc
    (∑ n ∈ s, (1 : ℝ) / (n : ℝ)^6) ≤
        ∑ n ∈ Finset.Icc K M, (1 : ℝ) / (n : ℝ)^6 := henlarge
    _ ≤ ∑ n ∈ Finset.Icc K M,
        (1 / ((n : ℝ) - 1)^5 - 1 / (n : ℝ)^5) := hsixth
    _ = 1 / ((K : ℝ) - 1)^5 - 1 / (M : ℝ)^5 := htel M hKM
    _ ≤ 1 / ((K : ℝ) - 1)^5 := by
      linarith [one_div_pos.mpr (pow_pos hM0 5)]

/-- Every finite sum of positive reciprocal sixth powers is at most two. -/
theorem finite_positive_sixth_sum
    (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n) :
    ∑ n ∈ s, (1 : ℝ) / (n : ℝ)^6 ≤ 2 := by
  by_cases h1 : 1 ∈ s
  · have htail := finite_sixth_tail (s.erase 1) 2 (by omega) (by
      intro n hn
      have hns := Finset.mem_of_mem_erase hn
      have hn1 := Finset.ne_of_mem_erase hn
      have hn0 := hs n hns
      omega)
    have hdecomp := Finset.add_sum_erase s
      (fun n ↦ (1 : ℝ) / (n : ℝ)^6) h1
    norm_num at hdecomp htail ⊢
    linarith
  · have htail := finite_sixth_tail s 2 (by omega) (by
      intro n hn
      have hn0 := hs n hn
      have hn1 : n ≠ 1 := by
        intro heq
        apply h1
        simpa [heq] using hn
      omega)
    norm_num at htail ⊢
    linarith

/-- A finite sum over positive multiples of `p` scales by `p⁻⁶`. -/
theorem finite_multiple_sixth_sum
    (s : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (hs : ∀ n ∈ s, 0 < n ∧ p ∣ n) :
    ∑ n ∈ s, (1 : ℝ) / (n : ℝ)^6 ≤
      2 / (p : ℝ)^6 := by
  have hrec : ∀ n ∈ s, n = p * (n / p) := by
    intro n hn
    exact (Nat.mul_div_cancel' (hs n hn).2).symm
  have hquot : ∀ n ∈ s, 0 < n / p := by
    intro n hn
    have hnpos := (hs n hn).1
    have heq := hrec n hn
    nlinarith
  have hinj : ∀ n ∈ s, ∀ k ∈ s, n / p = k / p → n = k := by
    intro n hn k hk heq
    rw [hrec n hn, hrec k hk, heq]
  have hmass := finite_positive_sixth_sum (s.image (fun n => n / p)) (by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact hquot n hn)
  rw [Finset.sum_image hinj] at hmass
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsum : (∑ n ∈ s, (1 : ℝ) / (n : ℝ)^6) =
      (1 / (p : ℝ)^6) * ∑ n ∈ s, (1 : ℝ) / ((n / p : ℕ) : ℝ)^6 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnR : ((n : ℕ) : ℝ) = (p : ℝ) * ((n / p : ℕ) : ℝ) := by
      exact_mod_cast hrec n hn
    rw [hnR]
    field_simp
  rw [hsum]
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ)^6)
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hscaled

/-- Splitting roots into the large tail and roots having a divisor above `N`
gives the retained-root sixth-power estimate. -/
theorem retained_root_sixth_sum
    (s : Finset ℕ) (N : ℕ) (hN : 2 ≤ N)
    (hspos : ∀ n ∈ s, 0 < n)
    (hcover : ∀ n ∈ s,
      N^2 ≤ n ∨ ∃ p : ℕ, N < p ∧ p ∣ n) :
    ∑ n ∈ s, (1 : ℝ) / (n : ℝ)^6 ≤
      3 / (N : ℝ)^5 := by
  let A := s.filter (fun n => N ^ 2 ≤ n)
  let B := s.filter (fun n => n < N ^ 2)
  let P := Finset.Icc (N + 1) (s.sup id)
  have hsplit :
      (∑ n ∈ s, (1 : ℝ) / (n : ℝ)^6) =
        (∑ n ∈ A, (1 : ℝ) / (n : ℝ)^6) +
          ∑ n ∈ B, (1 : ℝ) / (n : ℝ)^6 := by
    simpa only [A, B, not_le] using
      (Finset.sum_filter_add_sum_filter_not s (fun n => N ^ 2 ≤ n)
        (fun n => (1 : ℝ) / (n : ℝ)^6)).symm
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hAraw := finite_sixth_tail A (N ^ 2) (by nlinarith) (by
    intro n hn
    exact (Finset.mem_filter.mp hn).2)
  have hden : (N : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) - 1 := by
    norm_num [Nat.cast_pow]
    nlinarith
  have hpowden : (N : ℝ)^5 ≤ (((N ^ 2 : ℕ) : ℝ) - 1)^5 :=
    pow_le_pow_left₀ (by positivity) hden 5
  have hA : (∑ n ∈ A, (1 : ℝ) / (n : ℝ)^6) ≤ 1 / (N : ℝ)^5 := by
    exact hAraw.trans (one_div_le_one_div_of_le (by positivity) hpowden)
  have hBcover : ∀ n ∈ B, ∃ p ∈ P, p ∣ n := by
    intro n hn
    have hnparts := Finset.mem_filter.mp hn
    obtain ⟨hnS, hnlt⟩ := hnparts
    rcases hcover n hnS with hnlarge | ⟨p, hpN, hpdiv⟩
    · omega
    · refine ⟨p, ?_, hpdiv⟩
      apply Finset.mem_Icc.mpr
      constructor
      · omega
      · calc
          p ≤ n := Nat.le_of_dvd (hspos n hnS) hpdiv
          _ ≤ s.sup id := Finset.le_sup (f := id) hnS
  have hcover_sum :
      (∑ n ∈ B, (1 : ℝ) / (n : ℝ)^6) ≤
        ∑ p ∈ P, ∑ n ∈ B.filter (fun n => p ∣ n), (1 : ℝ) / (n : ℝ)^6 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨p, hp, hpn⟩ := hBcover n hn
    calc
      (1 : ℝ) / (n : ℝ)^6 =
          if p ∣ n then (1 : ℝ) / (n : ℝ)^6 else 0 := by simp [hpn]
      _ ≤ ∑ q ∈ P, if q ∣ n then (1 : ℝ) / (n : ℝ)^6 else 0 := by
        apply Finset.single_le_sum
          (f := fun q : ℕ => if q ∣ n then (1 : ℝ) / (n : ℝ)^6 else 0)
        · intro q _
          split_ifs <;> positivity
        · exact hp
  have hPtail := finite_sixth_tail P (N + 1) (by omega) (by
    intro p hp
    exact (Finset.mem_Icc.mp hp).1)
  have hB : (∑ n ∈ B, (1 : ℝ) / (n : ℝ)^6) ≤ 2 / (N : ℝ)^5 := by
    calc
      (∑ n ∈ B, (1 : ℝ) / (n : ℝ)^6) ≤
          ∑ p ∈ P, ∑ n ∈ B.filter (fun n => p ∣ n), (1 : ℝ) / (n : ℝ)^6 :=
        hcover_sum
      _ ≤ ∑ p ∈ P, (2 : ℝ) / (p : ℝ)^6 := by
        apply Finset.sum_le_sum
        intro p hp
        apply finite_multiple_sixth_sum _ p (by
          have hpN := (Finset.mem_Icc.mp hp).1
          omega)
        intro n hn
        obtain ⟨hnB, hdiv⟩ := Finset.mem_filter.mp hn
        have hnS := (Finset.mem_filter.mp hnB).1
        exact ⟨hspos n hnS, hdiv⟩
      _ = 2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ)^6 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 2 * (1 / (((N + 1 : ℕ) : ℝ) - 1)^5) :=
        mul_le_mul_of_nonneg_left hPtail (by norm_num)
      _ = 2 / (N : ℝ)^5 := by
        push_cast
        ring
  rw [hsplit]
  calc
    (∑ n ∈ A, (1 : ℝ) / (n : ℝ)^6) + ∑ n ∈ B, (1 : ℝ) / (n : ℝ)^6 ≤
        1 / (N : ℝ)^5 + 2 / (N : ℝ)^5 := add_le_add hA hB
    _ = 3 / (N : ℝ)^5 := by ring

end ReciprocalSquares
