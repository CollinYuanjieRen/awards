import MerLeanExperiment.ReciprocalBounds

namespace ReciprocalSquares

theorem sum_recip_sq_multiples_sq (F : Finset ℕ) (p : ℕ)
    (hp : 0 < p) (hF : ∀ n ∈ F, 0 < n ∧ p ^ 2 ∣ n) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 2 / (p : ℚ) ^ 4 := by
  have hp2 : 0 < p ^ 2 := pow_pos hp _
  have hrec : ∀ n ∈ F, n = p ^ 2 * (n / p ^ 2) := by
    intro n hn
    exact (Nat.mul_div_cancel' (hF n hn).2).symm
  have hquot : ∀ n ∈ F, 0 < n / p ^ 2 := by
    intro n hn
    have hnpos := (hF n hn).1
    have heq := hrec n hn
    nlinarith
  have hinj : ∀ n ∈ F, ∀ k ∈ F, n / p ^ 2 = k / p ^ 2 → n = k := by
    intro n hn k hk heq
    rw [hrec n hn, hrec k hk, heq]
  have hmass := sum_recip_sq_le_two (F.image (fun n => n / p ^ 2)) (by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact hquot n hn)
  rw [Finset.sum_image hinj] at hmass
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hsum : (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) =
      (1 / (p : ℚ) ^ 4) * ∑ n ∈ F, (1 : ℚ) / ((n / p ^ 2 : ℕ) : ℚ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnQ : ((n : ℕ) : ℚ) = (p : ℚ) ^ 2 * ((n / p ^ 2 : ℕ) : ℚ) := by
      exact_mod_cast hrec n hn
    rw [hnQ]
    field_simp
  rw [hsum]
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (by positivity : (0 : ℚ) ≤ 1 / (p : ℚ) ^ 4)
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hscaled

/-- A finite union bound for roots divisible by one of the selected prime
squares. No primality is needed for this estimate. -/
theorem sum_recip_sq_of_square_divisor_cover
    (F P : Finset ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hF : ∀ n ∈ F, 0 < n) (hP : ∀ p ∈ P, N < p)
    (hcover : ∀ n ∈ F, ∃ p ∈ P, p ^ 2 ∣ n) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 2 / (N : ℚ) ^ 3 := by
  have hcover_sum : (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤
      ∑ p ∈ P, ∑ n ∈ F.filter (fun n => p ^ 2 ∣ n), (1 : ℚ) / (n : ℚ) ^ 2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨p, hp, hpn⟩ := hcover n hn
    calc
      (1 : ℚ) / (n : ℚ) ^ 2 =
          if p ^ 2 ∣ n then (1 : ℚ) / (n : ℚ) ^ 2 else 0 := by simp [hpn]
      _ ≤ ∑ q ∈ P, if q ^ 2 ∣ n then (1 : ℚ) / (n : ℚ) ^ 2 else 0 := by
        apply Finset.single_le_sum
          (f := fun q : ℕ => if q ^ 2 ∣ n then (1 : ℚ) / (n : ℚ) ^ 2 else 0)
        · intro q _
          split_ifs <;> positivity
        · exact hp
  calc
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤
        ∑ p ∈ P, ∑ n ∈ F.filter (fun n => p ^ 2 ∣ n), (1 : ℚ) / (n : ℚ) ^ 2 :=
      hcover_sum
    _ ≤ ∑ p ∈ P, (2 : ℚ) / (p : ℚ) ^ 4 := by
      apply Finset.sum_le_sum
      intro p hp
      apply sum_recip_sq_multiples_sq _ p (by have := hP p hp; omega)
      intro n hn
      obtain ⟨hnF, hdiv⟩ := Finset.mem_filter.mp hn
      exact ⟨hF n hnF, hdiv⟩
    _ = 2 * ∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ 2 / (N : ℚ) ^ 3 := by
      have hscaled := mul_le_mul_of_nonneg_left (sum_recip_fourth_tail P N hN hP)
        (by norm_num : (0 : ℚ) ≤ 2)
      simpa only [div_eq_mul_inv, one_mul] using hscaled

end ReciprocalSquares
