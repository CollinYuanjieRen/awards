import MerLeanExperiment.SquareCoverage
import MerLeanExperiment.ReciprocalMultiples

namespace ReciprocalSquares

/-- The mass missing from any finite set of small roots is uniformly tiny.
This is a finite union bound over possible repeated large prime factors. -/
theorem small_omitted_square_mass_finset_le
    (N : ℕ) (hN : 2 ≤ N) (F : Finset ℕ)
    (hF : ∀ n ∈ F, 0 < n ∧ n < N ^ 3 ∧ n ∉ rootsZ N) :
    (∑ n ∈ F, (1 : ℚ) / (n : ℚ) ^ 2) ≤ 2 / (N : ℚ) ^ 3 := by
  apply sum_recip_sq_of_square_divisor_cover F (Finset.Ioo N (N ^ 3)) N
    (by omega) (fun n hn => (hF n hn).1)
    (fun p hp => (Finset.mem_Ioo.mp hp).1)
  intro n hn
  obtain ⟨hnpos, hbound, hmiss⟩ := hF n hn
  obtain ⟨p, _hprime, hNp, hdiv⟩ :=
    small_omitted_has_large_square_divisor N n hnpos hbound hmiss
  have hpp : p ∣ p ^ 2 := by rw [pow_two]; exact dvd_mul_right p p
  have hpn : p ≤ n := Nat.le_of_dvd hnpos (hpp.trans hdiv)
  exact ⟨p, Finset.mem_Ioo.mpr ⟨hNp, hpn.trans_lt hbound⟩, hdiv⟩

end ReciprocalSquares
