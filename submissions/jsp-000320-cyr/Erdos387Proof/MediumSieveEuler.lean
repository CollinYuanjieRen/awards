import Mathlib
import Erdos387Proof.BrunTruncation
import ErdosProblems.Erdos387.RoughHarmonicEstimate

/-!
# The medium-range local density and its Euler product

The first Euler factor loses at most `2^(4*k)` when primes below `4*k`
are removed. The logarithmic estimate is the already-proved elementary
harmonic/Euler-product inequality, not a Mertens asymptotic assumption.
-/

namespace Erdos387Proof.MediumSieveEuler

open Erdos387
open scoped BigOperators

noncomputable def alpha (k p : ℕ) : ℝ :=
  ((k : ℝ) + 1) / p - (k : ℝ) / (p : ℝ) ^ 2

noncomputable def windowPrimes (k z : ℕ) : Finset ℕ :=
  z.primesBelow.filter (fun p => 4 * k ≤ p)

theorem mem_windowPrimes {k z p : ℕ} :
    p ∈ windowPrimes k z ↔ p.Prime ∧ 4 * k ≤ p ∧ p < z := by
  simp only [windowPrimes, Finset.mem_filter, Nat.mem_primesBelow]
  tauto

/-- The local density belongs to the half interval, including `k=0`. -/
theorem alpha_bounds {k p : ℕ} (hp : p.Prime) (hkp : 4 * k ≤ p) :
    0 ≤ alpha k p ∧ alpha k p ≤ 1 / 2 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hnum : (2 : ℝ) * ((k : ℝ) + 1) ≤ p := by
    have hn : 2 * (k + 1) ≤ p := by
      by_cases hk : k = 0
      · simpa [hk] using hp.two_le
      · omega
    exact_mod_cast hn
  have heq : alpha k p = (((k : ℝ) + 1) * p - k) / (p : ℝ)^2 := by
    unfold alpha
    field_simp
  constructor
  · rw [heq]
    apply div_nonneg _ (sq_nonneg _)
    nlinarith [mul_nonneg hk0 (show 0 ≤ (p : ℝ) - 1 by linarith)]
  · calc
      alpha k p ≤ ((k : ℝ) + 1) / p :=
        sub_le_self _ (div_nonneg hk0 (sq_nonneg _))
      _ ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)

/-- Exact local factorization; no primality condition is needed. -/
theorem one_sub_alpha (k p : ℕ) :
    1 - alpha k p = (1 - (1 : ℝ) / p) * (1 - (k : ℝ) / p) := by
  simp only [alpha, div_eq_mul_inv]
  ring

theorem eulerProduct_alpha (P : Finset ℕ) (k : ℕ) :
    finiteEulerProduct P (alpha k) =
      (∏ p ∈ P, (1 - (1 : ℝ) / p)) *
        ∏ p ∈ P, (1 - (k : ℝ) / p) := by
  simp only [finiteEulerProduct, one_sub_alpha, Finset.prod_mul_distrib]

/-- The finite Euler factor at a prime is in `[1/2,1]`. -/
theorem prime_euler_factor_bounds {p : ℕ} (hp : p.Prime) :
    1 / 2 ≤ 1 - (1 : ℝ) / p ∧ 1 - (1 : ℝ) / p ≤ 1 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hb := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpR
  constructor
  · norm_num at hb
    rw [one_div (p : ℝ)]
    linarith
  · exact sub_le_self _ (by positivity)

/-- All-primes logarithmic upper bound, including the endpoints `z=0,1`. -/
theorem log_mul_fullEuler_le_one (z : ℕ) :
    Real.log z * (∏ p ∈ z.primesBelow, (1 - (1 : ℝ) / p)) ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  have h := RoughHarmonic.log_mul_preSieveSingularSeries_le_one (z - 1)
  change Real.log ((z - 1 + 1 : ℕ) : ℝ) *
    (∏ p ∈ (z - 1 + 1).primesBelow, (1 - (1 : ℝ) / p)) ≤ 1 at h
  simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz)] using h

/-- Removing primes below `4*k` costs a completely explicit fixed factor. -/
theorem windowEuler_le_pow_mul_fullEuler (k z : ℕ) :
    (∏ p ∈ windowPrimes k z, (1 - (1 : ℝ) / p)) ≤
      (2 : ℝ) ^ (4 * k) * ∏ p ∈ z.primesBelow, (1 - (1 : ℝ) / p) := by
  classical
  let Q := z.primesBelow.filter (fun p => p < 4 * k)
  let f : ℕ → ℝ := fun p => 1 - (1 : ℝ) / p
  have hQcard : Q.card ≤ 4 * k := by
    apply le_trans (Finset.card_le_card (show Q ⊆ Finset.range (4 * k) from ?_))
      (by simp)
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  have hQpos : 0 ≤ ∏ p ∈ Q, f p := by
    apply Finset.prod_nonneg
    intro p hp
    have hb := prime_euler_factor_bounds
      (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1)
    dsimp [f]
    linarith [hb.1]
  have hcost : 1 ≤ (2 : ℝ) ^ (4 * k) * ∏ p ∈ Q, f p := by
    calc
      (1 : ℝ) ≤ ∏ p ∈ Q, (2 * f p) := by
        apply Finset.one_le_prod
        intro p hp
        have hb := prime_euler_factor_bounds
          (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1)
        dsimp [f]
        linarith [hb.1]
      _ = (2 : ℝ) ^ Q.card * ∏ p ∈ Q, f p := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hQcard) hQpos
  have hsplit :
      (∏ p ∈ windowPrimes k z, f p) * (∏ p ∈ Q, f p) =
        ∏ p ∈ z.primesBelow, f p := by
    simpa only [windowPrimes, Q, not_le] using
      Finset.prod_filter_mul_prod_filter_not z.primesBelow (fun p => 4 * k ≤ p) f
  have hWnonneg : 0 ≤ ∏ p ∈ windowPrimes k z, f p := by
    apply Finset.prod_nonneg
    intro p hp
    have hb := prime_euler_factor_bounds (mem_windowPrimes.mp hp).1
    dsimp [f]
    linarith [hb.1]
  change (∏ p ∈ windowPrimes k z, f p) ≤ (2 : ℝ)^(4*k) * ∏ p ∈ z.primesBelow, f p
  calc
    _ = (∏ p ∈ windowPrimes k z, f p) * 1 := by ring
    _ ≤ (∏ p ∈ windowPrimes k z, f p) *
        ((2 : ℝ)^(4*k) * ∏ p ∈ Q, f p) :=
      mul_le_mul_of_nonneg_left hcost hWnonneg
    _ = _ := by rw [← hsplit]; ring

/-- Uniform multiplicative form avoids division at small `z`. -/
theorem log_mul_windowEuler_le (k z : ℕ) :
    Real.log z * (∏ p ∈ windowPrimes k z, (1 - (1 : ℝ) / p)) ≤
      (2 : ℝ) ^ (4 * k) := by
  have hlog : 0 ≤ Real.log (z : ℝ) := by
    by_cases hz : z = 0
    · simp [hz]
    · apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  calc
    _ ≤ Real.log z * ((2 : ℝ) ^ (4 * k) *
        ∏ p ∈ z.primesBelow, (1 - (1 : ℝ) / p)) :=
      mul_le_mul_of_nonneg_left (windowEuler_le_pow_mul_fullEuler k z) hlog
    _ = (2 : ℝ) ^ (4 * k) *
        (Real.log z * ∏ p ∈ z.primesBelow, (1 - (1 : ℝ) / p)) := by ring
    _ ≤ (2 : ℝ) ^ (4 * k) * 1 :=
      mul_le_mul_of_nonneg_left (log_mul_fullEuler_le_one z) (by positivity)
    _ = _ := by ring

/-- Explicit logarithmic bound after deleting the small primes. -/
theorem windowEuler_le_div_log (k : ℕ) {z : ℕ} (hz : 2 ≤ z) :
    (∏ p ∈ windowPrimes k z, (1 - (1 : ℝ) / p)) ≤
      (2 : ℝ) ^ (4 * k) / Real.log z := by
  have hzR : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  apply (le_div_iff₀ (Real.log_pos hzR)).mpr
  simpa only [mul_comm] using log_mul_windowEuler_le k z

/-- The actual coupled Euler product retains the original k-shift factor. -/
theorem eulerProduct_window_alpha_le (k : ℕ) {z : ℕ} (hz : 2 ≤ z) :
    finiteEulerProduct (windowPrimes k z) (alpha k) ≤
      ((2 : ℝ) ^ (4 * k) / Real.log z) *
        ∏ p ∈ windowPrimes k z, (1 - (k : ℝ) / p) := by
  rw [eulerProduct_alpha]
  apply mul_le_mul_of_nonneg_right (windowEuler_le_div_log k hz)
  apply Finset.prod_nonneg
  intro p hp
  have hmem := mem_windowPrimes.mp hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hmem.1.pos
  have hkp : (k : ℝ) ≤ p := by exact_mod_cast (show k ≤ p by omega)
  exact sub_nonneg.mpr ((div_le_one hpR).mpr hkp)

/-- The previously proved finite Brun window applies to the actual density. -/
theorem brun_window_bounds (k z : ℕ) {L : ℕ} (hL : Even L) :
    0 < finiteEulerProduct (windowPrimes k z) (alpha k) ∧
      finiteEulerProduct (windowPrimes k z) (alpha k) ≤
        brunSubsetSum (windowPrimes k z) (alpha k) L ∧
      brunSubsetSum (windowPrimes k z) (alpha k) L ≤
        finiteEulerProduct (windowPrimes k z) (alpha k) *
          (1 + ((2 : ℝ) ^ (L + 1))⁻¹ *
            Real.exp (4 * ∑ p ∈ windowPrimes k z, alpha k p)) := by
  apply BrunTruncation.brunSubsetSum_bounds_of_even _ _ hL
  intro p hp
  have hmem := mem_windowPrimes.mp hp
  exact alpha_bounds hmem.1 hmem.2.1

end Erdos387Proof.MediumSieveEuler
