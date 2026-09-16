import MerLeanExperiment.SquareFactorization
import MerLeanExperiment.LcmSupport

namespace ReciprocalSquares

theorem squareD_gt_scale (N : ℕ) (hN : 2 ≤ N) :
    ∀ d ∈ squareD N, N ^ 2 < d := by
  intro d hd
  obtain ⟨hdZ, hdE⟩ := Finset.mem_sdiff.mp hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hdZ
  have hapos := rootsZ_pos ha
  by_contra hnot
  have haN : a ≤ N := by nlinarith
  have haPrefix : a ∈ prefixRoots N := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      nlinarith
    · exact Nat.mem_smoothNumbers_of_lt hapos (by omega)
  exact hdE (Finset.mem_image.mpr ⟨a, haPrefix, rfl⟩)

theorem erased_mul_prime_sq_mem_squareD (N e p : ℕ) (hN : 2 ≤ N)
    (he : e ∈ squareE N) (hp : p ∈ largePrimes N) :
    e * p ^ 2 ∈ squareD N := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
  have hbSmooth : b ∈ smoothRoots N := prefixRoots_subset_smoothRoots N (by omega) hb
  have hpPrime := largePrimes_prime hp
  have hroot : b * p ∈ rootsZ N := by
    apply Finset.mem_image.mpr
    refine ⟨(b, {p}), Finset.mem_product.mpr ⟨hbSmooth, ?_⟩, ?_⟩
    · simpa using hp
    · simp [rootProduct]
  apply Finset.mem_sdiff.mpr
  constructor
  · apply Finset.mem_image.mpr
    exact ⟨b * p, hroot, by ring⟩
  · intro hE
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hE
    have hsquare : c ^ 2 = (b * p) ^ 2 := by nlinarith [heq]
    have hcprod : c = b * p := Nat.pow_left_injective (by decide : 2 ≠ 0) hsquare
    have hpc : p ∣ c := by rw [hcprod]; exact dvd_mul_left p b
    have hcSmooth := (Finset.mem_filter.mp hc).2
    have hsmall := Nat.mem_smoothNumbers'.mp hcSmooth p hpPrime hpc
    have hlarge := (Finset.mem_filter.mp hp).2
    omega

theorem squareZ_dvd_squareD_lcm (N p : ℕ) (hN : 2 ≤ N)
    (hp : p ∈ largePrimes N) :
    ∀ z ∈ squareZ N, z ∣ (squareD N).lcm id := by
  apply dvd_lcm_sdiff_of_cover
  intro e he
  exact ⟨e * p ^ 2, erased_mul_prime_sq_mem_squareD N e p hN he hp, dvd_mul_right e _⟩

end ReciprocalSquares
