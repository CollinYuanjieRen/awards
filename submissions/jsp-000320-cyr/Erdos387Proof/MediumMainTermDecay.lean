import Mathlib
import Erdos387Proof.MediumSieveEuler
import ErdosProblems.Erdos387.SubpowerAnalytic

/-!
# Decay of the actual medium-range Euler main factor

The denominator is the existing refined sieve density with cutoff `2*k`.
The change from that cutoff to `4*k` is bounded explicitly. No decay or
prime-distribution estimate is assumed in the final statement.
-/

namespace Erdos387Proof.MediumMainTermDecay

open Erdos387 Erdos387.CoverBPZ MediumSieveEuler
open scoped BigOperators

/-- The exact density used by the existing refined sieve. -/
noncomputable def refinedDensity {B K : ℕ} (S : BPZSection6Input B K) (z : ℕ) : ℝ :=
  finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
    (fun p => binomialSieveNu S.k p)

theorem mem_refined_primeFactors {B K z p : ℕ} (S : BPZSection6Input B K) :
    p ∈ (refinedSievePrimeProduct S z).primeFactors ↔
      p.Prime ∧ 2 * S.k ≤ p ∧ p < z := by
  constructor
  · intro hp
    have h := prime_mem_refinedSievePrimes_of_dvd_product S
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    exact ⟨h.1, by omega, h.2.2⟩
  · rintro ⟨hp, hlow, hhigh⟩
    have hk := S.hk3
    have hmem : p ∈ sievePrimes (2 * S.k - 1) z :=
      mem_sievePrimes.mpr ⟨hp, by omega, hhigh⟩
    apply Nat.mem_primeFactors.mpr
    refine ⟨hp, ?_, (refinedSievePrimeProduct_pos S z).ne'⟩
    exact Finset.dvd_prod_of_mem id hmem

theorem refinedDensity_eq_prod {B K : ℕ} (S : BPZSection6Input B K) (z : ℕ) :
    refinedDensity S z =
      ∏ p ∈ (refinedSievePrimeProduct S z).primeFactors, (1 - (S.k : ℝ) / p) := by
  unfold refinedDensity finiteEulerProduct
  apply Finset.prod_congr rfl
  intro p hp
  dsimp only
  rw [binomialSieveNu_prime (Nat.prime_of_mem_primeFactors hp)]

theorem refined_factor_half_le {B K z p : ℕ} (S : BPZSection6Input B K)
    (hp : p ∈ (refinedSievePrimeProduct S z).primeFactors) :
    (1 / 2 : ℝ) ≤ 1 - (S.k : ℝ) / p := by
  have hmem := (mem_refined_primeFactors S).mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hmem.1.pos
  have hlow : (2 : ℝ) * S.k ≤ p := by exact_mod_cast hmem.2.1
  have hdiv : (S.k : ℝ) / p ≤ 1 / 2 :=
    (div_le_iff₀ hp0).mpr (by linarith)
  linarith

theorem refinedDensity_pos {B K : ℕ} (S : BPZSection6Input B K) (z : ℕ) :
    0 < refinedDensity S z := by
  rw [refinedDensity_eq_prod]
  apply Finset.prod_pos
  intro p hp
  have := refined_factor_half_le S hp
  linarith

/-- The omitted primes between `2*k` and `4*k` have uniformly bounded cost. -/
theorem window_shift_euler_le_refined {B K : ℕ} (S : BPZSection6Input B K) (z : ℕ) :
    (∏ p ∈ windowPrimes S.k z, (1 - (S.k : ℝ) / p)) ≤
      (2 : ℝ) ^ (4 * S.k) * refinedDensity S z := by
  classical
  let P := (refinedSievePrimeProduct S z).primeFactors
  let W := windowPrimes S.k z
  let Q := P \ W
  let f : ℕ → ℝ := fun p => 1 - (S.k : ℝ) / p
  have hWP : W ⊆ P := by
    intro p hp
    have h := mem_windowPrimes.mp hp
    exact (mem_refined_primeFactors S).mpr ⟨h.1, by omega, h.2.2⟩
  have hQcard : Q.card ≤ 4 * S.k := by
    apply le_trans (Finset.card_le_card (show Q ⊆ Finset.range (4 * S.k) from ?_))
      (by simp)
    intro p hp
    obtain ⟨hpP, hpW⟩ := Finset.mem_sdiff.mp hp
    have hmem := (mem_refined_primeFactors S).mp hpP
    apply Finset.mem_range.mpr
    by_contra hn
    exact hpW (mem_windowPrimes.mpr ⟨hmem.1, by omega, hmem.2.2⟩)
  have hQnonneg : 0 ≤ ∏ p ∈ Q, f p := by
    apply Finset.prod_nonneg
    intro p hp
    have := refined_factor_half_le S (Finset.mem_sdiff.mp hp).1
    dsimp [f]
    linarith
  have hcost : 1 ≤ (2 : ℝ) ^ (4 * S.k) * ∏ p ∈ Q, f p := by
    calc
      (1 : ℝ) ≤ ∏ p ∈ Q, (2 * f p) := by
        apply Finset.one_le_prod
        intro p hp
        have := refined_factor_half_le S (Finset.mem_sdiff.mp hp).1
        dsimp [f]
        linarith
      _ = (2 : ℝ) ^ Q.card * ∏ p ∈ Q, f p := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hQcard) hQnonneg
  have hsplit : (∏ p ∈ Q, f p) * (∏ p ∈ W, f p) = ∏ p ∈ P, f p :=
    Finset.prod_sdiff hWP
  have hWnonneg : 0 ≤ ∏ p ∈ W, f p := by
    apply Finset.prod_nonneg
    intro p hp
    have := refined_factor_half_le S (hWP hp)
    dsimp [f]
    linarith
  rw [refinedDensity_eq_prod]
  change (∏ p ∈ W, f p) ≤ (2 : ℝ)^(4*S.k) * ∏ p ∈ P, f p
  calc
    _ = 1 * (∏ p ∈ W, f p) := by ring
    _ ≤ ((2 : ℝ)^(4*S.k) * ∏ p ∈ Q, f p) * (∏ p ∈ W, f p) :=
      mul_le_mul_of_nonneg_right hcost hWnonneg
    _ = _ := by rw [mul_assoc, hsplit]

/-- Coupled Euler density relative to the actual refined sieve density. -/
theorem coupledEuler_le_refined_div_log {B K : ℕ}
    (S : BPZSection6Input B K) {z : ℕ} (hz : 2 ≤ z) :
    finiteEulerProduct (windowPrimes S.k z) (alpha S.k) ≤
      ((2 : ℝ) ^ (8 * S.k) / Real.log z) * refinedDensity S z := by
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  calc
    _ ≤ ((2 : ℝ) ^ (4 * S.k) / Real.log z) *
        ∏ p ∈ windowPrimes S.k z, (1 - (S.k : ℝ) / p) :=
      eulerProduct_window_alpha_le S.k hz
    _ ≤ ((2 : ℝ) ^ (4 * S.k) / Real.log z) *
        ((2 : ℝ) ^ (4 * S.k) * refinedDensity S z) :=
      mul_le_mul_of_nonneg_left (window_shift_euler_le_refined S z) (by positivity)
    _ = _ := by
      have he : 8 * S.k = 4 * S.k + 4 * S.k := by omega
      rw [he, pow_add]
      ring

/-- The existing uniform rough harmonic theorem gives the needed quadratic
bound at the full endpoint X, uniformly for every positive scale parameter. -/
theorem exists_full_roughMass_quadratic_bound {k : ℕ} (hk : 0 < k) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 0 < N →
      roughReciprocalMass (SubpowerScale.z N k) (SubpowerScale.X N k) ≤
        A * (N : ℝ)^2 := by
  obtain ⟨K, _, hK⟩ := RoughHarmonic.exists_uniform_roughReciprocalMass_le_envelope
  let A : ℝ := 1 + SubpowerScale.roughEnvelopeOffset K
  have hA : 0 < A := by
    have := SubpowerScale.roughEnvelopeOffset_nonneg K
    dsimp [A]
    linarith
  refine ⟨A, hA, ?_⟩
  intro N hN
  have henv := SubpowerScale.roughLogRatioEnvelope_le_mul_square
    (K := K) (D := 1) (T := SubpowerScale.X N k) hN hk
    (by rw [SubpowerScale.log_X_div_log_z_eq_square hN hk]; simp)
  exact (hK _ _ (SubpowerScale.two_le_z hN hk)).trans (by simpa [A] using henv)

/-- Exact normalization by the original refined sieve density. -/
noncomputable def normalizedMainFactor {B K : ℕ}
    (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  (finiteEulerProduct (windowPrimes S.k (SubpowerScale.z N S.k)) (alpha S.k) *
    roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) ^ (S.k - 1)) /
      refinedDensity S (SubpowerScale.z N S.k)

/-- Fully derived fixed-k inverse-fifth-power bound. The bound holds for
all positive N, so in particular gives the requested eventual saving. -/
theorem exists_normalizedMainFactor_le_inv_fifth {B K : ℕ}
    (S : BPZSection6Input B K) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      normalizedMainFactor S N ≤ C / (N : ℝ)^5 := by
  have hk : 0 < S.k := by have := S.hk3; omega
  obtain ⟨A, hA, hmass⟩ := exists_full_roughMass_quadratic_bound hk
  let C : ℝ := (2 : ℝ) ^ (8 * S.k) * A ^ (S.k - 1) /
    ((BPZScale.xExp S.k : ℝ) * Real.log 2)
  have hx : (0 : ℝ) < BPZScale.xExp S.k := by
    unfold BPZScale.xExp
    positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hz := SubpowerScale.two_le_z hN hk
  have hzlog : 0 < Real.log (SubpowerScale.z N S.k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < SubpowerScale.z N S.k by omega))
  have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
  have hRnonneg : 0 ≤ roughReciprocalMass (SubpowerScale.z N S.k)
      (SubpowerScale.X N S.k) := by
    unfold roughReciprocalMass
    positivity
  have hpow := pow_le_pow_left₀ hRnonneg (hmass N hN) (S.k - 1)
  have hE := coupledEuler_le_refined_div_log S hz
  have hbound := mul_le_mul hE hpow
    (pow_nonneg hRnonneg _) (by positivity)
  have hNpow : ((N : ℝ)^2)^(S.k-1) * (N : ℝ)^5 =
      (N : ℝ)^(2*S.k+3) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hratio : ((N : ℝ)^2)^(S.k-1) / (N : ℝ)^(2*S.k+3) =
      1 / (N : ℝ)^5 := by
    rw [← hNpow]
    field_simp
  have heq :
      (((2 : ℝ)^(8*S.k) / Real.log (SubpowerScale.z N S.k : ℝ)) *
        refinedDensity S (SubpowerScale.z N S.k)) *
          (A * (N : ℝ)^2)^(S.k-1) =
        refinedDensity S (SubpowerScale.z N S.k) * (C / (N : ℝ)^5) := by
    rw [mul_pow]
    calc
      _ = refinedDensity S (SubpowerScale.z N S.k) * C *
          (((N : ℝ)^2)^(S.k-1) / (N : ℝ)^(2*S.k+3)) := by
        rw [SubpowerScale.log_z_eq]
        unfold SubpowerScale.roughPower
        dsimp [C]
        push_cast
        field_simp
      _ = _ := by rw [hratio]; ring
  unfold normalizedMainFactor
  apply (div_le_iff₀ hV).mpr
  calc
    _ ≤ _ := hbound
    _ = _ := by rw [heq]; ring

end Erdos387Proof.MediumMainTermDecay
