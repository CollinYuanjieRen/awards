import MerLeanExperiment.SquareConstruction
import Mathlib.Data.Nat.Factorization.Basic

namespace ReciprocalSquares

/-- The part of `n` supported on prime factors at most `N`. -/
def lowPart (N n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≤ N), p ^ n.factorization p

/-- The prime factors of `n` that are larger than `N`. -/
def highSupport (N n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => N < p)

/-- Splitting the factorization at `N` reconstructs `n` when high exponents are at most one. -/
theorem lowPart_mul_highSupport (N n : ℕ) (hn : 0 < n)
    (hlarge : ∀ p ∈ n.primeFactors, N < p → n.factorization p ≤ 1) :
    lowPart N n * (highSupport N n).prod id = n := by
  have hall :
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
      Nat.prod_factorization_pow_eq_self hn.ne'
  have hhigh :
      (highSupport N n).prod id =
        ∏ p ∈ n.primeFactors.filter (fun p => N < p),
          p ^ n.factorization p := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpF : p ∈ n.primeFactors := (Finset.mem_filter.mp hp).1
    have hpgt : N < p := (Finset.mem_filter.mp hp).2
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpF
    have hppos : 0 < n.factorization p :=
      hpprime.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hpF)
    have hpleone : n.factorization p ≤ 1 := hlarge p hpF hpgt
    have hpone : n.factorization p = 1 := by
      omega
    simp [hpone]
  rw [lowPart, hhigh]
  calc
    (∏ p ∈ n.primeFactors.filter (fun p => p ≤ N), p ^ n.factorization p) *
        ∏ p ∈ n.primeFactors.filter (fun p => N < p), p ^ n.factorization p =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      simpa only [not_le] using Finset.prod_filter_mul_prod_filter_not
        n.primeFactors (fun p => p ≤ N) (fun p => p ^ n.factorization p)
    _ = n := hall

/-- The low part has no prime factor greater than `N`. -/
theorem lowPart_smooth (N n : ℕ) : lowPart N n ∈ Nat.smoothNumbers (N + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro q hq hqdiv
  unfold lowPart at hqdiv
  rw [hq.prime.dvd_finsetProd_iff] at hqdiv
  obtain ⟨p, hp, hqpow⟩ := hqdiv
  have hpF : p ∈ n.primeFactors := (Finset.mem_filter.mp hp).1
  have hpN : p ≤ N := (Finset.mem_filter.mp hp).2
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpF
  have hqp : q ∣ p := hq.dvd_of_dvd_pow hqpow
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hpprime).mp hqp
  omega

/-- The low part divides the original number. -/
theorem lowPart_dvd (N n : ℕ) (hn : 0 < n) : lowPart N n ∣ n := by
  have hprod :
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
      Nat.prod_factorization_pow_eq_self hn.ne'
  have hdvd :
      (∏ p ∈ n.primeFactors.filter (fun p => p ≤ N), p ^ n.factorization p) ∣
        ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  unfold lowPart
  rwa [hprod] at hdvd

/-- A bounded number with squarefree high-prime support belongs to `rootsZ`. -/
theorem mem_rootsZ_of_large_factorization_le_one (N n : ℕ)
    (hn : 0 < n) (hbound : n < N ^ 3)
    (hlarge : ∀ p ∈ n.primeFactors, N < p → n.factorization p ≤ 1) :
    n ∈ rootsZ N := by
  have hlow_dvd : lowPart N n ∣ n := lowPart_dvd N n hn
  have hlow_le : lowPart N n ≤ n := Nat.le_of_dvd hn hlow_dvd
  have hlow_mem : lowPart N n ∈ smoothRoots N := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (hlow_le.trans_lt hbound), lowPart_smooth N n⟩
  have hhigh_subset : highSupport N n ⊆ largePrimes N := by
    intro p hp
    have hpF : p ∈ n.primeFactors := (Finset.mem_filter.mp hp).1
    have hpgt : N < p := (Finset.mem_filter.mp hp).2
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpF
    have hple : p ≤ n := Nat.le_of_mem_primeFactors hpF
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_primesBelow.mpr ⟨hple.trans_lt hbound, hpprime⟩, hpgt⟩
  apply Finset.mem_image.mpr
  refine ⟨(lowPart N n, highSupport N n), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    exact ⟨hlow_mem, Finset.mem_powerset.mpr hhigh_subset⟩
  · exact lowPart_mul_highSupport N n hn hlarge

/-- A bounded positive root omitted from `rootsZ` has a repeated prime factor above `N`. -/
theorem small_omitted_has_large_square_divisor (N n : ℕ)
    (hn : 0 < n) (hbound : n < N ^ 3) (hmiss : n ∉ rootsZ N) :
    ∃ p, p.Prime ∧ N < p ∧ p ^ 2 ∣ n := by
  by_contra hnone
  push Not at hnone
  apply hmiss
  apply mem_rootsZ_of_large_factorization_le_one N n hn hbound
  intro p hpF hpgt
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpF
  by_contra hfac
  have htwo : 2 ≤ n.factorization p := by omega
  have hpdvd : p ^ 2 ∣ n :=
    (hpprime.pow_dvd_iff_le_factorization hn.ne').mpr htwo
  exact (hnone p hpprime hpgt) hpdvd

end ReciprocalSquares
