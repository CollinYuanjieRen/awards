import Erdos439Power.CyclicPolynomialBound
import Erdos439Power.NormalizedPolynomial

open scoped BigOperators
open Erdos439 Erdos439.PowerDecay

namespace Erdos439Power

/-- Once `L` contains the small primes, every nontrivial reduced rational
frequency has a uniformly small complete average. -/
theorem complete_normalizedPower_bound (k L w q a : ℕ) [NeZero q]
    (hk : 2 ≤ k) (hL : 0 < L) (hkw : k ≤ w) (hq : 1 < q)
    (ha : a.Coprime q)
    (hsmall : ∀ p : ℕ, Nat.Prime p → p ≤ w → p ∣ L) :
    ‖𝔼 x : ZMod q, polynomialPhase q a (normalizedPowerPolynomial k L) x‖ ^
        (2 ^ (k - 1)) ≤ ((k - 1 : ℕ) : ℝ) / w := by
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (show q ≠ 1 by omega)
  by_cases hpL : p ∣ L
  · have hzero := sum_normalizedPowerPolynomial_eq_zero_of_smallPrime k L q a p
      (by omega) hp hpq hpL ha
    simp only [Fintype.expect_eq_sum_div_card, polynomialPhase, hzero, zero_div, norm_zero,
      zero_pow (by positivity : 2 ^ (k - 1) ≠ 0)]
    positivity
  · have hwp : w < p := by
      by_contra h
      exact hpL (hsmall p hp (by omega))
    have hap : (a : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hp.coprime_iff_not_dvd.mp (ha.of_dvd_right hpq).symm
    have hbound := norm_expect_polynomialPhase_pow_le q a p k (by omega) hp hpq hap
      (normalizedPowerPolynomial k L) (natDegree_normalizedPowerPolynomial k L hk hL)
      (by omega) (by omega)
      (normalizedPowerPolynomial_leadingCoeff_prime_ne_zero k L p hk hL hp (by omega) hpL)
    refine hbound.trans ?_
    exact div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast (show 0 < w by omega)) (by exact_mod_cast hwp.le)

/-- A fixed positive dilation makes all nontrivial rational complete sums
as small as desired. The choice is independent of the rational denominator. -/
theorem exists_dilation_complete_sums (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ q : ℕ, ∀ a : ℕ, ∀ hq : 1 < q,
      letI : NeZero q := ⟨by omega⟩
      a.Coprime q →
        ‖𝔼 x : ZMod q, polynomialPhase q a (normalizedPowerPolynomial k L) x‖ ≤ ε := by
  obtain ⟨w₀, hw₀⟩ := exists_nat_gt (((k - 1 : ℕ) : ℝ) / ε ^ (2 ^ (k - 1)))
  let w := max k w₀
  let L := w.factorial
  have hL : 0 < L := Nat.factorial_pos _
  refine ⟨L, hL, ?_⟩
  intro q a hq
  letI : NeZero q := ⟨by omega⟩
  intro ha
  have hsmall : ∀ p : ℕ, Nat.Prime p → p ≤ w → p ∣ L := by
    intro p hp hpw
    exact Nat.dvd_factorial hp.pos hpw
  have hbound := complete_normalizedPower_bound k L w q a hk hL (le_max_left _ _) hq ha hsmall
  have hwpos : (0 : ℝ) < w := by
    exact_mod_cast (show 0 < w by dsimp [w]; omega)
  have hratio : ((k - 1 : ℕ) : ℝ) / w ≤ ε ^ (2 ^ (k - 1)) := by
    apply (div_le_iff₀ hwpos).mpr
    have hwreal : (w₀ : ℝ) ≤ w := by exact_mod_cast le_max_right k w₀
    have hεpow : 0 < ε ^ (2 ^ (k - 1)) := pow_pos hε _
    have h := (div_lt_iff₀ hεpow).mp hw₀
    nlinarith
  exact le_of_pow_le_pow_left₀ (by positivity : 2 ^ (k - 1) ≠ 0) hε.le
    (hbound.trans hratio)

end Erdos439Power
