import Mathlib

namespace ReciprocalSquares

/-- A reciprocal square is bounded by the adjacent telescoping difference. -/
private theorem recip_sq_le_telescope (x : ℚ) (hx : 2 ≤ x) :
    1 / x ^ 2 ≤ 1 / (x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hid : 1 / (x - 1) - 1 / x = 1 / ((x - 1) * x) := by
    field_simp
    ring
  rw [hid]
  apply one_div_le_one_div_of_le (mul_pos hx1 hx0)
  nlinarith

/-- A reciprocal fourth power is bounded by a cubic telescoping difference. -/
private theorem recip_fourth_le_telescope (x : ℚ) (hx : 2 ≤ x) :
    1 / x ^ 4 ≤ 1 / (x - 1) ^ 3 - 1 / x ^ 3 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  rw [le_sub_iff_add_le]
  have hid : 1 / x ^ 4 + 1 / x ^ 3 = (1 + x) / x ^ 4 := by
    field_simp
  rw [hid]
  apply (div_le_div_iff₀ (pow_pos hx0 4) (pow_pos hx1 3)).2
  have hprod : 0 ≤ x * (x - 1) * (x + 1) := by positivity
  nlinarith

/-- A finite reciprocal-square tail is bounded by its first telescoping term. -/
theorem sum_recip_sq_tail (F : Finset ℕ) (K : ℕ)
    (hK : 2 ≤ K) (hF : ∀ n ∈ F, K ≤ n) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 1 / ((K : ℚ) - 1) := by
  by_cases hFempty : F = ∅
  · simp [hFempty]
    omega
  have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
  let M := F.sup id
  have hKM : K ≤ M := by
    calc
      K ≤ hFne.choose := hF hFne.choose hFne.choose_spec
      _ ≤ F.sup id := Finset.le_sup (f := id) hFne.choose_spec
      _ = M := rfl
  have hsub : F ⊆ Finset.Icc K M := by
    intro n hn
    have hnM : n ≤ M := by
      simpa [M] using Finset.le_sup (f := id) hn
    exact Finset.mem_Icc.mpr ⟨hF n hn, hnM⟩
  have henlarge :
      (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤
        ∑ n ∈ Finset.Icc K M, (1 : ℚ) / (n : ℚ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn _
    have hn0 : 0 < (n : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < K) (Finset.mem_Icc.mp hn).1)
    positivity
  have hsquare :
      (∑ n ∈ Finset.Icc K M, (1 : ℚ) / (n : ℚ) ^ 2) ≤
        ∑ n ∈ Finset.Icc K M,
          (1 / ((n : ℚ) - 1) - 1 / (n : ℚ)) := by
    apply Finset.sum_le_sum
    intro n hn
    apply recip_sq_le_telescope
    exact_mod_cast hK.trans (Finset.mem_Icc.mp hn).1
  have htel : ∀ L : ℕ, K ≤ L →
      (∑ n ∈ Finset.Icc K L,
        (1 / ((n : ℚ) - 1) - 1 / (n : ℚ))) =
        1 / ((K : ℚ) - 1) - 1 / (L : ℚ) := by
    intro L hKL
    induction L, hKL using Nat.le_induction with
    | base => simp
    | succ L hKL ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hKL), ih]
      push_cast
      ring
  have hM0 : 0 < (M : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < K) hKM)
  calc
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤
        ∑ n ∈ Finset.Icc K M, (1 : ℚ) / (n : ℚ) ^ 2 := henlarge
    _ ≤ ∑ n ∈ Finset.Icc K M,
        (1 / ((n : ℚ) - 1) - 1 / (n : ℚ)) := hsquare
    _ = 1 / ((K : ℚ) - 1) - 1 / (M : ℚ) := htel M hKM
    _ ≤ 1 / ((K : ℚ) - 1) := by
      linarith [one_div_pos.mpr hM0]

theorem sum_recip_sq_le_two (F : Finset ℕ)
    (hF : ∀ n ∈ F, 0 < n) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 2 := by
  by_cases h1 : 1 ∈ F
  · have htail := sum_recip_sq_tail (F.erase 1) 2 (by omega) (by
      intro n hn
      have hnF := Finset.mem_of_mem_erase hn
      have hn1 := Finset.ne_of_mem_erase hn
      have hn0 := hF n hnF
      omega)
    have hdecomp := Finset.add_sum_erase F
      (fun n ↦ (1 : ℚ) / (n : ℚ) ^ 2) h1
    norm_num at hdecomp htail ⊢
    linarith
  · have htail := sum_recip_sq_tail F 2 (by omega) (by
      intro n hn
      have hn0 := hF n hn
      have hn1 : n ≠ 1 := by
        intro heq
        apply h1
        simpa [heq] using hn
      omega)
    norm_num at htail ⊢
    linarith

theorem sum_recip_sq_le_three_quarters (F : Finset ℕ)
    (hF : ∀ n ∈ F, 2 ≤ n) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 3 / 4 := by
  by_cases h2 : 2 ∈ F
  · have htail := sum_recip_sq_tail (F.erase 2) 3 (by omega) (by
      intro n hn
      have hnF := Finset.mem_of_mem_erase hn
      have hn2 := Finset.ne_of_mem_erase hn
      have hnlow := hF n hnF
      omega)
    have hdecomp := Finset.add_sum_erase F
      (fun n ↦ (1 : ℚ) / (n : ℚ) ^ 2) h2
    norm_num at hdecomp htail ⊢
    linarith
  · have htail := sum_recip_sq_tail F 3 (by omega) (by
      intro n hn
      have hnlow := hF n hn
      have hn2 : n ≠ 2 := by
        intro heq
        apply h2
        simpa [heq] using hn
      omega)
    norm_num at htail ⊢
    linarith

theorem sum_recip_fourth_tail (P : Finset ℕ) (N : ℕ)
    (hN : 1 ≤ N) (hP : ∀ p ∈ P, N < p) :
    (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 4) ≤ 1 / (N : ℚ) ^ 3 := by
  by_cases hPempty : P = ∅
  · simp [hPempty]
  have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPempty
  let M := P.sup id
  have hNM : N + 1 ≤ M := by
    calc
      N + 1 ≤ hPne.choose := by
        exact Nat.succ_le_iff.mpr (hP hPne.choose hPne.choose_spec)
      _ ≤ P.sup id := Finset.le_sup (f := id) hPne.choose_spec
      _ = M := rfl
  have hsub : P ⊆ Finset.Icc (N + 1) M := by
    intro p hp
    have hpM : p ≤ M := by
      simpa [M] using Finset.le_sup (f := id) hp
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_iff.mpr (hP p hp), hpM⟩
  have henlarge :
      (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 4) ≤
        ∑ p ∈ Finset.Icc (N + 1) M, (1 : ℚ) / (p : ℚ) ^ 4 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hp0 : 0 < (p : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N + 1) (Finset.mem_Icc.mp hp).1)
    positivity
  have hfourth :
      (∑ p ∈ Finset.Icc (N + 1) M, (1 : ℚ) / (p : ℚ) ^ 4) ≤
        ∑ p ∈ Finset.Icc (N + 1) M,
          (1 / ((p : ℚ) - 1) ^ 3 - 1 / (p : ℚ) ^ 3) := by
    apply Finset.sum_le_sum
    intro p hp
    apply recip_fourth_le_telescope
    have hplow := (Finset.mem_Icc.mp hp).1
    have hp2 : 2 ≤ p := by
      omega
    exact_mod_cast hp2
  have htel : ∀ L : ℕ, N + 1 ≤ L →
      (∑ p ∈ Finset.Icc (N + 1) L,
        (1 / ((p : ℚ) - 1) ^ 3 - 1 / (p : ℚ) ^ 3)) =
        1 / (N : ℚ) ^ 3 - 1 / (L : ℚ) ^ 3 := by
    intro L hNL
    induction L, hNL using Nat.le_induction with
    | base =>
      push_cast
      simp
    | succ L hNL ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hNL), ih]
      push_cast
      ring
  have hM0 : 0 < (M : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N + 1) hNM)
  calc
    (∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 4) ≤
        ∑ p ∈ Finset.Icc (N + 1) M, (1 : ℚ) / (p : ℚ) ^ 4 := henlarge
    _ ≤ ∑ p ∈ Finset.Icc (N + 1) M,
        (1 / ((p : ℚ) - 1) ^ 3 - 1 / (p : ℚ) ^ 3) := hfourth
    _ = 1 / (N : ℚ) ^ 3 - 1 / (M : ℚ) ^ 3 := htel M hNM
    _ ≤ 1 / (N : ℚ) ^ 3 := by
      linarith [one_div_pos.mpr (pow_pos hM0 3)]

end ReciprocalSquares
