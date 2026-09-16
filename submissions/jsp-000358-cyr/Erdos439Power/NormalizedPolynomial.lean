import Erdos439Power.PolynomialPrime
import Erdos439Power.SmallPrimeCancellation

open scoped BigOperators Polynomial
open Erdos439 Erdos439.PowerDecay

namespace Erdos439Power

/-- The nonlinear part has an explicit integral factor `L`. -/
lemma normalizedPowerPolynomial_eq_X_add_mul (k L : ℕ) :
    ∃ Q : ℤ[X], normalizedPowerPolynomial k L =
      Polynomial.X + Q * Polynomial.C (L : ℤ) := by
  let Q : ℤ[X] := ∑ j ∈ Finset.Icc 2 k,
    Polynomial.C ((k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
      L ^ (j - 2) : ℕ) : ℤ) * Polynomial.X ^ j
  refine ⟨Q, ?_⟩
  unfold normalizedPowerPolynomial Q
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  have hexp : j - 1 = (j - 2) + 1 := by omega
  rw [hexp, pow_succ]
  push_cast
  simp only [Polynomial.C_mul]
  ring

lemma sum_normalizedPowerPolynomial_eq_zero_of_smallPrime
    (k L q a p : ℕ) [NeZero q] (hq : 0 < q)
    (hp : Nat.Prime p) (hpq : p ∣ q) (hpL : p ∣ L) (ha : a.Coprime q) :
    (∑ x : ZMod q, ZMod.stdAddChar ((a : ZMod q) *
      (normalizedPowerPolynomial k L).eval₂ (Int.castRingHom (ZMod q)) x)) = 0 := by
  obtain ⟨Q, hQ⟩ := normalizedPowerPolynomial_eq_X_add_mul k L
  rw [hQ]
  simpa using smallPrime_polynomial_character_sum_eq_zero q p a L 1 Q hq hp hpq hpL ha

lemma normalizedPowerPolynomial_leadingCoeff_prime_ne_zero
    (k L p : ℕ) (hk : 2 ≤ k) (hL : 0 < L) (hp : Nat.Prime p)
    (hkp : k < p) (hpL : ¬ p ∣ L) :
    ((normalizedPowerPolynomial k L).leadingCoeff : ZMod p) ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [Polynomial.leadingCoeff, natDegree_normalizedPowerPolynomial k L hk hL,
    coeff_normalizedPowerPolynomial_top k L hk]
  push_cast
  have hkn : (k : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff k p).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) hkp)
  have h2n : (2 : ZMod p) ≠ 0 := by
    have hnot : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr hnot
  have hLn : (L : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff L p).not.mpr hpL
  have hDn : (powerDerivative k : ZMod p) ≠ 0 := by
    simpa [powerDerivative] using mul_ne_zero hkn (pow_ne_zero _ h2n)
  exact mul_ne_zero (pow_ne_zero _ hDn) (pow_ne_zero _ hLn)

end Erdos439Power
