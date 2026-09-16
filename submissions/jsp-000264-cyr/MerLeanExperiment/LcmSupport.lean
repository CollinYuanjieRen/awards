import MerLeanExperiment.RationalNumerator

namespace ReciprocalSquares

theorem lcm_eq_of_dvd_cover (Z D : Finset ℕ)
    (hDZ : D ⊆ Z) (hcover : ∀ z ∈ Z, ∃ d ∈ D, z ∣ d) :
    Z.lcm id = D.lcm id := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro z hz
    obtain ⟨d, hd, hzd⟩ := hcover z hz
    exact hzd.trans (Finset.dvd_lcm hd)
  · exact Finset.lcm_mono hDZ

theorem dvd_lcm_sdiff_of_cover (Z E : Finset ℕ)
    (hcover : ∀ e ∈ E, ∃ d ∈ Z \ E, e ∣ d) :
    ∀ z ∈ Z, z ∣ (Z \ E).lcm id := by
  intro z hz
  by_cases he : z ∈ E
  · obtain ⟨d, hd, hzd⟩ := hcover z he
    exact hzd.trans (Finset.dvd_lcm hd)
  · exact Finset.dvd_lcm (Finset.mem_sdiff.mpr ⟨hz, he⟩)

theorem finset_lcm_pos (Z : Finset ℕ) (hZ : ∀ z ∈ Z, 0 < z) :
    0 < Z.lcm id := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun z hz => (hZ z hz).ne')

/-- A positive residual reciprocal mass has a positive natural numerator
over any positive common multiple; no inclusion between `S` and `Y` is needed. -/
theorem exists_pos_residual_numerator (Z Y S : Finset ℕ) (m : ℕ)
    (hm : 0 < m) (hZ : ∀ n ∈ Z, 0 < n)
    (hdiv : ∀ n ∈ Z, n ∣ m) (hY : Y ⊆ Z) (hS : S ⊆ Z)
    (hr : 0 < recipSumQ Y - recipSumQ S) :
    ∃ k : ℕ, 0 < k ∧ (k : ℚ) = (m : ℚ) * (recipSumQ Y - recipSumQ S) := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hYnum := numerator_eq_mul_recipSum Z Y m hZ hdiv hY
  have hSnum := numerator_eq_mul_recipSum Z S m hZ hdiv hS
  have hnumQ : ((∑ n ∈ S, m / n : ℕ) : ℚ) <
      ((∑ n ∈ Y, m / n : ℕ) : ℚ) := by
    rw [hSnum, hYnum]
    apply mul_lt_mul_of_pos_left _ hmQ
    linarith
  have hnum : (∑ n ∈ S, m / n : ℕ) < (∑ n ∈ Y, m / n : ℕ) := by
    exact_mod_cast hnumQ
  refine ⟨(∑ n ∈ Y, m / n) - (∑ n ∈ S, m / n), by omega, ?_⟩
  rw [Nat.cast_sub hnum.le, hYnum, hSnum, mul_sub]

end ReciprocalSquares
