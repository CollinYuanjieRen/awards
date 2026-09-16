import Erdos387Proof.MediumEndpointError
import Erdos387Proof.MediumMainTermDecay

/-! The full finite endpoint envelope, at depth `2*N`, tends to zero after
normalization by `X * V / M`. Here `V` is the original refined sieve density.
All subset-count and divisor-count factors are retained. -/

namespace Erdos387Proof.MediumEndpointDecay

open Erdos387 Erdos387.CoverBPZ MediumMainTermDecay
open Filter
open scoped BigOperators Topology

/-- The actual original density has an eventual reciprocal bound on the
subpower scale, derived from the existing prime-count and Brun estimates. -/
theorem eventually_one_le_pow_mul_refinedDensity {B K : ℕ}
    (S : BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ (2 : ℝ) ^ (N ^ 2) * refinedDensity S (SubpowerScale.z N S.k) := by
  obtain ⟨C, hC, hcheb⟩ := PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  obtain ⟨a, b, hdepth⟩ := exists_refined_tail_and_euler_reciprocal_depth hC hcheb S
  filter_upwards [eventually_ge_atTop (2 * (SubpowerScale.depthSlope a b S.k + 1) + 1)]
    with N hN
  have hL := SubpowerScale.logarithmicBrunDepth_succ_le_square hN
  have hrecip := (hdepth (SubpowerScale.z N S.k)).2.2
  change 1 ≤ (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b
    (SubpowerScale.z N S.k) * refinedDensity S (SubpowerScale.z N S.k) at hrecip
  exact hrecip.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (by omega))
    (refinedDensity_pos S _).le)

def fixedBaseExponent (k : ℕ) : ℕ := Nat.log 2 (4 * k) + 1

def endpointExponent (N k : ℕ) : ℕ :=
  SubpowerScale.roughPower N k * (2 * N) + 2 * N ^ 2 + fixedBaseExponent k * (2 * N)

/-- Every exponential cost fits in one scale power with a remaining gap N. -/
theorem endpointExponent_add_self_le_scalePower {N k : ℕ}
    (hN1 : 1 ≤ N)
    (hN : 2 * BPZScale.xExp k + 2 + 2 * fixedBaseExponent k + 1 ≤ N) :
    endpointExponent N k + N ≤ SubpowerScale.scalePower N k := by
  have hpow1 : N ≤ N ^ (2 * k + 4) := by
    simpa using Nat.pow_le_pow_right hN1 (by omega : 1 ≤ 2 * k + 4)
  have hpow2 : N ^ 2 ≤ N ^ (2 * k + 4) :=
    Nat.pow_le_pow_right hN1 (by omega)
  have hrough : SubpowerScale.roughPower N k * (2 * N) =
      2 * BPZScale.xExp k * N ^ (2 * k + 4) := by
    unfold SubpowerScale.roughPower
    rw [show 2 * k + 4 = (2 * k + 3) + 1 by omega, pow_succ]
    ring
  unfold endpointExponent
  rw [hrough]
  calc
    _ ≤ 2 * BPZScale.xExp k * N ^ (2 * k + 4) +
        2 * N ^ (2 * k + 4) + fixedBaseExponent k * (2 * N ^ (2 * k + 4)) +
        N ^ (2 * k + 4) := by gcongr
    _ = (2 * BPZScale.xExp k + 2 + 2 * fixedBaseExponent k + 1) *
        N ^ (2 * k + 4) := by ring
    _ ≤ N * N ^ (2 * k + 4) := Nat.mul_le_mul_right _ hN
    _ = SubpowerScale.scalePower N k := by
      unfold SubpowerScale.scalePower
      rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega, pow_succ]
      ring

theorem pow_scalePower_le_medium (N : ℕ) {k : ℕ} (hk : 0 < k) :
    2 ^ SubpowerScale.scalePower N k ≤ SubpowerScale.medium N k := by
  have hm : 1 ≤ BPZScale.mediumExp k := Nat.succ_le_of_lt (by
    unfold BPZScale.mediumExp
    positivity)
  change SubpowerScale.base N k ≤ SubpowerScale.base N k ^ BPZScale.mediumExp k
  simpa using Nat.pow_le_pow_right (show 1 ≤ SubpowerScale.base N k by
    unfold SubpowerScale.base
    exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))) hm

/-- All exponential factors, including the density reciprocal, at the
specified depth and prime-factor budget. -/
noncomputable def endpointScaleFactor {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  (SubpowerScale.z N S.k : ℝ) ^ (2 * N) * (2 : ℝ) ^ (N ^ 2) *
    (4 * (S.k : ℝ)) ^ (2 * N) /
      ((SubpowerScale.medium N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k))

theorem endpointScaleFactor_nonneg {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    0 ≤ endpointScaleFactor S N := by
  unfold endpointScaleFactor
  apply div_nonneg (by positivity)
  exact mul_nonneg (by positivity) (refinedDensity_pos S _).le

theorem eventually_endpointScaleFactor_le_inv_pow {B K : ℕ}
    (S : BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop, endpointScaleFactor S N ≤ 1 / (2 : ℝ) ^ N := by
  have hk : 0 < S.k := by have := S.hk3; omega
  filter_upwards [eventually_one_le_pow_mul_refinedDensity S,
    eventually_ge_atTop (1 : ℕ),
    eventually_ge_atTop (2 * BPZScale.xExp S.k + 2 + 2 * fixedBaseExponent S.k + 1)]
    with N hVrecip hN1 hN
  have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
  have hmed : (0 : ℝ) < SubpowerScale.medium N S.k := by
    unfold SubpowerScale.medium BPZScale.medium SubpowerScale.base
    positivity
  have htwo : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hkbase : (4 * (S.k : ℝ)) ≤ (2 : ℝ) ^ fixedBaseExponent S.k := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (4 * S.k)).le
  have hkpow : (4 * (S.k : ℝ)) ^ (2 * N) ≤
      (2 : ℝ) ^ (fixedBaseExponent S.k * (2 * N)) := by
    calc
      _ ≤ ((2 : ℝ) ^ fixedBaseExponent S.k) ^ (2 * N) :=
        pow_le_pow_left₀ (by positivity) hkbase _
      _ = _ := (pow_mul _ _ _).symm
  have hzpow : (SubpowerScale.z N S.k : ℝ) ^ (2 * N) =
      (2 : ℝ) ^ (SubpowerScale.roughPower N S.k * (2 * N)) := by
    simp [SubpowerScale.z, pow_mul]
  let U : ℝ := (SubpowerScale.z N S.k : ℝ) ^ (2 * N) *
    (2 : ℝ) ^ (N ^ 2) * (4 * (S.k : ℝ)) ^ (2 * N)
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hU : U * (2 : ℝ) ^ (N ^ 2) ≤ (2 : ℝ) ^ endpointExponent N S.k := by
    calc
      _ ≤ ((SubpowerScale.z N S.k : ℝ) ^ (2 * N) * (2 : ℝ) ^ (N ^ 2) *
          (2 : ℝ) ^ (fixedBaseExponent S.k * (2 * N))) * (2 : ℝ) ^ (N ^ 2) := by
        dsimp [U]
        gcongr
      _ = _ := by
        rw [hzpow, ← pow_add, ← pow_add, ← pow_add]
        congr 1
        unfold endpointExponent
        ring
  have hden : (2 : ℝ) ^ (endpointExponent N S.k + N) ≤ SubpowerScale.medium N S.k := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
      (endpointExponent_add_self_le_scalePower hN1 hN)).trans (pow_scalePower_le_medium N hk)
  have hmain : U * (2 : ℝ) ^ N ≤
      (SubpowerScale.medium N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) := by
    calc
      _ ≤ (U * (2 : ℝ) ^ N) *
          ((2 : ℝ) ^ (N ^ 2) * refinedDensity S (SubpowerScale.z N S.k)) :=
        le_mul_of_one_le_right (by positivity) hVrecip
      _ = (U * (2 : ℝ) ^ (N ^ 2)) * (2 : ℝ) ^ N *
          refinedDensity S (SubpowerScale.z N S.k) := by ring
      _ ≤ (2 : ℝ) ^ endpointExponent N S.k * (2 : ℝ) ^ N *
          refinedDensity S (SubpowerScale.z N S.k) := by gcongr
      _ ≤ _ := by rw [← pow_add]; exact mul_le_mul_of_nonneg_right hden hV.le
  unfold endpointScaleFactor
  exact (div_le_div_iff₀ (mul_pos hmed hV) htwo).mpr (by simpa [U] using hmain)

/-- Total finite endpoint envelope after summing the complementary reciprocal
mass and normalizing by X*V/M. The 16 includes the tent mass bound 4X and
the harmonic endpoint constant 4. -/
noncomputable def normalizedEndpointEnvelope {B K : ℕ}
    (S : BPZSection6Input B K) (M N : ℕ) : ℝ :=
  16 * M.divisors.card * (2 * (N : ℝ) + 1) *
    roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) ^ (S.k - 1) *
      endpointScaleFactor S N

/-- The unnormalized total endpoint envelope after the positive reciprocal
sum over complementary tuples. -/
noncomputable def totalEndpointEnvelope {B K : ℕ}
    (S : BPZSection6Input B K) (M N : ℕ) : ℝ :=
  (16 * (SubpowerScale.X N S.k : ℝ) / M) * M.divisors.card *
    (2 * (N : ℝ) + 1) *
    roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) ^ (S.k - 1) *
    (SubpowerScale.z N S.k : ℝ) ^ (2 * N) * (2 : ℝ) ^ (N ^ 2) *
    (4 * (S.k : ℝ)) ^ (2 * N) / (SubpowerScale.medium N S.k : ℝ)

/-- Exact cancellation of the X/M scale, using the original refined density. -/
theorem totalEndpointEnvelope_div_sieveScale {B K : ℕ}
    (S : BPZSection6Input B K) {M : ℕ} (hM : 0 < M) (N : ℕ) :
    totalEndpointEnvelope S M N /
        ((SubpowerScale.X N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) / M) =
      normalizedEndpointEnvelope S M N := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hXR : (SubpowerScale.X N S.k : ℝ) ≠ 0 := by
    exact_mod_cast (SubpowerScale.X_pos N S.k).ne'
  have hVR := (refinedDensity_pos S (SubpowerScale.z N S.k)).ne'
  have hmed : (SubpowerScale.medium N S.k : ℝ) ≠ 0 := by
    unfold SubpowerScale.medium BPZScale.medium SubpowerScale.base
    positivity
  unfold totalEndpointEnvelope normalizedEndpointEnvelope endpointScaleFactor
  field_simp

theorem normalizedEndpointEnvelope_nonneg {B K : ℕ}
    (S : BPZSection6Input B K) (M N : ℕ) :
    0 ≤ normalizedEndpointEnvelope S M N := by
  unfold normalizedEndpointEnvelope
  apply mul_nonneg _ (endpointScaleFactor_nonneg S N)
  unfold roughReciprocalMass
  positivity

/-- No analytic bound is a premise: both the rough mass and the reciprocal
of the actual refined density are obtained from proved source estimates. -/
theorem tendsto_normalizedEndpointEnvelope_zero {B K : ℕ}
    (S : BPZSection6Input B K) (M : ℕ) :
    Tendsto (normalizedEndpointEnvelope S M) atTop (𝓝 0) := by
  have hk : 0 < S.k := by have := S.hk3; omega
  obtain ⟨A, hA, hmass⟩ := exists_full_roughMass_quadratic_bound hk
  let C : ℝ := 48 * M.divisors.card * A ^ (S.k - 1)
  have hlim : Tendsto (fun N : ℕ => C * ((N : ℝ) ^ (2 * (S.k - 1) + 1) /
      (2 : ℝ) ^ N)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt
      (2 * (S.k - 1) + 1) (by norm_num : (1 : ℝ) < 2)).const_mul C
  apply squeeze_zero' (g := fun N : ℕ => C * ((N : ℝ) ^ (2 * (S.k - 1) + 1) /
    (2 : ℝ) ^ N)) _ _ hlim
  · exact Filter.Eventually.of_forall (normalizedEndpointEnvelope_nonneg S M)
  · filter_upwards [eventually_endpointScaleFactor_le_inv_pow S,
      eventually_ge_atTop (1 : ℕ)] with N hscale hN
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hR0 : 0 ≤ roughReciprocalMass (SubpowerScale.z N S.k)
        (SubpowerScale.X N S.k) := by unfold roughReciprocalMass; positivity
    have hR := pow_le_pow_left₀ hR0 (hmass N (by omega)) (S.k - 1)
    unfold normalizedEndpointEnvelope
    calc
      _ ≤ 16 * M.divisors.card * (3 * (N : ℝ)) *
          (A * (N : ℝ) ^ 2) ^ (S.k - 1) * (1 / (2 : ℝ) ^ N) := by
        apply mul_le_mul
        · apply mul_le_mul
          · gcongr
            linarith
          · exact hR
          · positivity
          · positivity
        · exact hscale
        · exact endpointScaleFactor_nonneg S N
        · positivity
      _ = _ := by
        dsimp [C]
        rw [mul_pow, ← pow_mul, pow_succ]
        ring

/-- The same decay in the unnormalized finite-error notation, divided by
the actual original sieve scale. -/
theorem tendsto_totalEndpointEnvelope_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) {M : ℕ} (hM : 0 < M) :
    Tendsto (fun N => totalEndpointEnvelope S M N /
      ((SubpowerScale.X N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) / M))
      atTop (𝓝 0) := by
  simpa only [totalEndpointEnvelope_div_sieveScale S hM] using
    tendsto_normalizedEndpointEnvelope_zero S M

/-- Any additional fixed coefficient, for instance a factor depending on B,
preserves the derived endpoint decay. -/
theorem tendsto_const_mul_normalizedEndpointEnvelope_zero {B K : ℕ}
    (S : BPZSection6Input B K) (M : ℕ) (C : ℝ) :
    Tendsto (fun N => C * normalizedEndpointEnvelope S M N) atTop (𝓝 0) := by
  simpa using (tendsto_normalizedEndpointEnvelope_zero S M).const_mul C

end Erdos387Proof.MediumEndpointDecay
