import Erdos439Power.PolynomialPhase
import Erdos439Power.PolynomialPrime
import Erdos439Power.PrimeResidueCount

open scoped BigOperators Polynomial

namespace Erdos439Power

/-- Cyclic differencing costs at most one bad residue class per degree.
This bound uses a single prime divisor of the modulus. -/
theorem cyclicWeylMean_polynomial_le (q a p : ℕ) [NeZero q]
    (hq : 0 < q) (hp : Nat.Prime p) (hpq : p ∣ q)
    (ha : (a : ZMod p) ≠ 0) (d : ℕ) (P : ℤ[X])
    (hdegree : P.natDegree = d + 1) (hdp : d + 1 < p)
    (hlc : (P.leadingCoeff : ZMod p) ≠ 0) :
    cyclicWeylMean (polynomialPhase q a P) d ≤ (d : ℝ) / p := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  induction d generalizing P with
  | zero =>
      have hfreq : (a : ZMod q) * (P.leadingCoeff : ZMod q) ≠ 0 := by
        have hz : (((a : ℤ) * P.leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
          simpa using mul_ne_zero ha hlc
        simpa using intCast_ne_zero_of_prime_factor hpq ((a : ℤ) * P.leadingCoeff) hz
      simp only [cyclicWeylMean,
        expect_polynomialPhase_eq_zero_of_natDegree_eq_one q a P hdegree hfreq,
        norm_zero, Nat.cast_zero, zero_div, le_refl]
  | succ d ih =>
      change (𝔼 h : ZMod q, cyclicWeylMean
        (cyclicDifference (polynomialPhase q a P) h) d) ≤ ((d + 1 : ℕ) : ℝ) / p
      calc
        (𝔼 h : ZMod q, cyclicWeylMean
            (cyclicDifference (polynomialPhase q a P) h) d) ≤
          𝔼 h : ZMod q, ((if p ∣ h.val then (1 : ℝ) else 0) + (d : ℝ) / p) := by
          apply Finset.expect_le_expect
          intro h _
          by_cases hbad : p ∣ h.val
          · simp only [if_pos hbad]
            have hunit : ∀ x, ‖cyclicDifference (polynomialPhase q a P) h x‖ ≤ 1 := by
              intro x
              simp [cyclicDifference]
            have hnonneg : (0 : ℝ) ≤ (d : ℝ) / p := by positivity
            exact (cyclicWeylMean_le_one _ hunit d).trans (by linarith)
          · simp only [if_neg hbad, zero_add, cyclicDifference_polynomialPhase]
            have hdata := shiftDifference_prime_data P h.val p hp
              (by omega) (by omega) hlc hbad
            exact ih _ (by omega) (by omega) hdata.2
        _ = ((d + 1 : ℕ) : ℝ) / p := by
          rw [Finset.expect_add_distrib, expect_indicator_dvd_val q p hq hp.pos hpq]
          simp only [Finset.expect_const, Finset.univ_nonempty, Nat.cast_add, Nat.cast_one]
          ring

/-- A complete polynomial character average is small when the modulus has
a large prime divisor at which its leading coefficient remains nonzero. -/
theorem norm_expect_polynomialPhase_pow_le (q a p k : ℕ) [NeZero q]
    (hq : 0 < q) (hp : Nat.Prime p) (hpq : p ∣ q)
    (ha : (a : ZMod p) ≠ 0) (P : ℤ[X])
    (hdegree : P.natDegree = k) (hk : 1 ≤ k) (hkp : k < p)
    (hlc : (P.leadingCoeff : ZMod p) ≠ 0) :
    ‖𝔼 x : ZMod q, polynomialPhase q a P x‖ ^ (2 ^ (k - 1)) ≤
      ((k - 1 : ℕ) : ℝ) / p := by
  exact (norm_expect_pow_le_cyclicWeylMean _ (k - 1)).trans
    (cyclicWeylMean_polynomial_le q a p hq hp hpq ha (k - 1) P (by omega)
      (by omega) hlc)

end Erdos439Power
