import MerLeanExperiment.SquareConstruction
import MerLeanExperiment.ReciprocalBounds
import MerLeanExperiment.RationalNumerator
import MerLeanExperiment.SixthPowerBounds

namespace ReciprocalSquares

/-- A finite set of squares greater than one has reciprocal mass at most three quarters. -/
theorem sum_square_recip_le_three_quarters (F : Finset ℕ)
    (hF : ∀ d ∈ F, 1 < d ∧ IsSquare d) :
    (∑ d ∈ F, (1 : ℚ) / (d : ℚ)) ≤ 3 / 4 := by
  have hroot : ∀ d ∈ F, Nat.sqrt d ^ 2 = d := by
    intro d hd
    obtain ⟨a, rfl⟩ := (hF d hd).2
    simp [Nat.sqrt_eq, pow_two]
  have hinj : ∀ d ∈ F, ∀ e ∈ F, Nat.sqrt d = Nat.sqrt e → d = e := by
    intro d hd e he heq
    rw [← hroot d hd, ← hroot e he, heq]
  have hmass := sum_recip_sq_le_three_quarters (F.image Nat.sqrt) (by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    have hdgt := (hF d hd).1
    have hsq := hroot d hd
    nlinarith)
  rw [Finset.sum_image hinj] at hmass
  have heq : (∑ d ∈ F, (1 : ℚ) / (Nat.sqrt d : ℚ) ^ 2) =
      ∑ d ∈ F, (1 : ℚ) / (d : ℚ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Nat.cast_pow, hroot d hd]
  rwa [heq] at hmass

/-- The square mass bound in the common rational reciprocal-sum notation. -/
theorem recipSumQ_square_le_three_quarters (F : Finset ℕ)
    (hF : ∀ d ∈ F, 1 < d ∧ IsSquare d) :
    recipSumQ F ≤ 3 / 4 :=
  sum_square_recip_le_three_quarters F hF

/-- The same finite square mass bound after casting into the reals. -/
theorem sum_square_recip_real_le_three_quarters (F : Finset ℕ)
    (hF : ∀ d ∈ F, 1 < d ∧ IsSquare d) :
    (∑ d ∈ F, (1 : ℝ) / (d : ℝ)) ≤ 3 / 4 := by
  have h : (recipSumQ F : ℝ) ≤ ((3 / 4 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (recipSumQ_square_le_three_quarters F hF)
  simpa [recipSumQ] using h

/-- The roots whose squares remain after erasing the exact smooth prefix. -/
def retainedRoots (N : ℕ) : Finset ℕ := rootsZ N \ prefixRoots N

/-- Taking squares commutes with removing the prefix, by injectivity on natural roots. -/
theorem squareD_eq_image_retainedRoots (N : ℕ) :
    squareD N = (retainedRoots N).image (fun n => n ^ 2) := by
  exact (Finset.image_sdiff (rootsZ N) (prefixRoots N)
    (Nat.pow_left_injective (by decide : 2 ≠ 0))).symm

/-- Every retained root is positive. -/
theorem retainedRoots_pos {N n : ℕ} (hn : n ∈ retainedRoots N) : 0 < n :=
  rootsZ_pos (Finset.mem_sdiff.mp hn).1

/-- A retained root below the prefix cutoff must have a prime divisor above the scale. -/
theorem retainedRoots_large_or_large_divisor {N n : ℕ}
    (hn : n ∈ retainedRoots N) :
    N ^ 2 ≤ n ∨ ∃ p : ℕ, N < p ∧ p ∣ n := by
  by_cases hlarge : N ^ 2 ≤ n
  · exact Or.inl hlarge
  · right
    by_contra hnone
    push Not at hnone
    have hsmooth : n ∈ Nat.smoothNumbers (N + 1) := by
      rw [Nat.mem_smoothNumbers']
      intro p _hp hpdiv
      by_contra hbound
      exact hnone p (by omega) hpdiv
    have hprefix : n ∈ prefixRoots N :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hsmooth⟩
    exact (Finset.mem_sdiff.mp hn).2 hprefix

/-- The cubic reciprocal moment of the remaining square denominators is small. -/
theorem squareD_recip_cube_sum_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ d ∈ squareD N, (1 : ℝ) / (d : ℝ) ^ 3) ≤
      3 / (N : ℝ) ^ 5 := by
  rw [squareD_eq_image_retainedRoots]
  rw [Finset.sum_image (fun a _ b _ hab =>
    Nat.pow_left_injective (by decide : 2 ≠ 0) hab)]
  simpa only [Nat.cast_pow, ← pow_mul] using
    retained_root_sixth_sum (retainedRoots N) N hN
      (fun _ hn => retainedRoots_pos hn)
      (fun _ hn => retainedRoots_large_or_large_divisor hn)

end ReciprocalSquares
