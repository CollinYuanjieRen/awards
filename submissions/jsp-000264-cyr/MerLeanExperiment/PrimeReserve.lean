import Mathlib

namespace ReciprocalSquares

open scoped BigOperators

/-- The primes in the interval `(K, 4K]`. -/
def widePrimes (K : ℕ) : Finset ℕ :=
  Nat.primesLE (4 * K) \ Nat.primesLE K

/-- An explicit linear bound for the logarithm beyond `512²`. -/
theorem log_le_div_256 {m : ℝ} (hm : 262144 ≤ m) :
    Real.log m ≤ m / 256 := by
  have hm0 : 0 < m := by linarith
  have hs : 512 ≤ Real.sqrt m := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hsq := Real.sq_sqrt hm0.le
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hm0)
  rw [Real.log_sqrt hm0.le] at hlog
  have hmul := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg m)
  nlinarith

/-- A finite Chebyshev estimate with a prescribed bound on the logarithm. -/
theorem widePrimes_card_mul_lower
    (K : ℕ) (m : ℝ) (hm : 8 ≤ m)
    (hk : 4 * m ^ 2 ≤ (K : ℝ))
    (hlog : Real.log (4 * (K : ℝ)) ≤ m / 8) :
    4 * (K : ℝ) ≤ m * ((widePrimes K).card : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hkm : m ≤ (K : ℝ) := by nlinarith
  have hk0 : 0 < (K : ℝ) := lt_of_lt_of_le hm0 hkm
  have hs0 : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
  have hs : 2 * m ≤ Real.sqrt (K : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq := Real.sq_sqrt hk0.le
  have hmul := mul_le_mul_of_nonneg_right hs hs0
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at this ⊢
    linarith
  have hlog2hi : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have := Real.log_pow (2 : ℝ) 2
    norm_num at this
    exact this
  have hsmall : Real.log (4 * (K : ℝ) + 1) ≤ (K : ℝ) / 4 := by
    calc
      Real.log (4 * (K : ℝ) + 1) ≤ Real.log (2 * (4 * (K : ℝ))) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 2 + Real.log (4 * (K : ℝ)) :=
        Real.log_mul (by norm_num) (by positivity)
      _ ≤ (K : ℝ) / 4 := by linarith
  have hsqrt : Real.sqrt (4 * (K : ℝ)) = 2 * Real.sqrt (K : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hlarge : 2 * Real.sqrt (4 * (K : ℝ)) * Real.log (4 * (K : ℝ)) ≤
      (K : ℝ) / 4 := by
    rw [hsqrt]
    have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4 * Real.sqrt (K : ℝ) by positivity)
    nlinarith
  have htheta : (K : ℝ) / 2 ≤
      Chebyshev.theta (4 * (K : ℝ)) - Chebyshev.theta (K : ℝ) := by
    have hlo := Chebyshev.theta_ge (4 * K)
    push_cast at hlo
    have hhi := Chebyshev.theta_le_log4_mul_x hk0.le
    rw [hlog4] at hhi
    have := mul_le_mul_of_nonneg_right hlog2lo hk0.le
    nlinarith
  have hsubset : Nat.primesLE K ⊆ Nat.primesLE (4 * K) :=
    Nat.primesLE_mono (by omega)
  have hsum : (∑ p ∈ widePrimes K, Real.log (p : ℝ)) =
      Chebyshev.theta (4 * (K : ℝ)) - Chebyshev.theta (K : ℝ) := by
    rw [widePrimes, Finset.sum_sdiff_eq_sub hsubset]
    rw [← Chebyshev.theta_eq_sum_primesLE_log, ← Chebyshev.theta_eq_sum_primesLE_log]
    push_cast
    rfl
  have hcard : (∑ p ∈ widePrimes K, Real.log (p : ℝ)) ≤
      ((widePrimes K).card : ℝ) * (m / 8) := by
    calc
      (∑ p ∈ widePrimes K, Real.log (p : ℝ)) ≤ ∑ _p ∈ widePrimes K, m / 8 := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Nat.mem_primesLE.1 (Finset.mem_sdiff.1 hp).1
        have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp'.2.pos
        have hpbound : (p : ℝ) ≤ 4 * (K : ℝ) := by exact_mod_cast hp'.1
        exact (Real.log_le_log hp0 hpbound).trans hlog
      _ = _ := by simp
  rw [hsum] at hcard
  nlinarith

/-- The logarithm bound holds uniformly throughout the needed interval. -/
theorem log_four_mul_le_eighth
    {m k : ℝ} (hm : 262144 ≤ m)
    (hkpos : 0 < k) (hk : k ≤ 4 * m ^ 20) :
    Real.log (4 * k) ≤ m / 8 := by
  have hm0 : 0 < m := by linarith
  have hlog2 : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by linarith)
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    have := Real.log_pow (2 : ℝ) 4
    norm_num at this
    exact this
  have hlog := log_le_div_256 hm
  calc
    Real.log (4 * k) ≤ Real.log (16 * m ^ 20) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = 4 * Real.log 2 + 20 * Real.log m := by
      rw [Real.log_mul (by norm_num) (by positivity), hlog16, Real.log_pow]
      norm_num
    _ ≤ m / 8 := by linarith

/-- An explicit, uniform reserve of primes for the integer-power scale. -/
theorem widePrimes_card_pure_power
    (M K : ℕ) (hM : 262144 ≤ M)
    (hlo : M ^ 10 ≤ K) (hhi : K ≤ 4 * (M ^ 10) ^ 2) :
    4 * M ^ 9 ≤ (widePrimes K).card := by
  have hm : (262144 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hm0 : (0 : ℝ) < M := by linarith
  have hm1 : (1 : ℝ) ≤ M := by linarith
  have hlo' : (M : ℝ) ^ 10 ≤ K := by exact_mod_cast hlo
  have hhi' : (K : ℝ) ≤ 4 * (M : ℝ) ^ 20 := by
    have hh : (K : ℝ) ≤ 4 * ((M : ℝ) ^ 10) ^ 2 := by exact_mod_cast hhi
    simpa only [← pow_mul] using hh
  have hk : 4 * (M : ℝ) ^ 2 ≤ (K : ℝ) := by
    have hfour : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
    calc
      4 * (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 * (M : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hfour (sq_nonneg _)
      _ = (M : ℝ) ^ 4 := by ring
      _ ≤ (M : ℝ) ^ 10 := pow_le_pow_right₀ hm1 (by decide)
      _ ≤ (K : ℝ) := hlo'
  have hk0 : (0 : ℝ) < K := lt_of_lt_of_le (pow_pos hm0 10) hlo'
  have hc := widePrimes_card_mul_lower K (M : ℝ) (by linarith) hk
    (log_four_mul_le_eighth hm hk0 hhi')
  have hcancel : (M : ℝ) * (4 * (M : ℝ) ^ 9) ≤
      (M : ℝ) * ((widePrimes K).card : ℝ) := by
    calc
      (M : ℝ) * (4 * (M : ℝ) ^ 9) = 4 * (M : ℝ) ^ 10 := by ring
      _ ≤ 4 * (K : ℝ) := by linarith
      _ ≤ _ := hc
  have hresult : (4 : ℝ) * (M : ℝ) ^ 9 ≤ ((widePrimes K).card : ℝ) := by
    nlinarith
  exact_mod_cast hresult

end ReciprocalSquares
