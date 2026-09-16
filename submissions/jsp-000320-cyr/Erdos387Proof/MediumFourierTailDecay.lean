import Erdos387Proof.MediumFourierTail
import Erdos387Proof.MediumEndpointDecay

/-! An integer cutoff H=z^(8N) makes the complete finite Fourier tail
negligible. Every fixed power of H remains subpower relative to X. -/

namespace Erdos387Proof.MediumFourierTailDecay

open Erdos387 Erdos387.CoverBPZ MediumMainTermDecay MediumFourierTail
open Filter
open scoped BigOperators Topology

/-- The cutoff is G^4 for the Brun support bound G=z^(2N). -/
def height (N k : ℕ) : ℕ := SubpowerScale.z N k ^ (8 * N)

theorem height_pos (N k : ℕ) : 0 < height N k := by
  unfold height SubpowerScale.z
  positivity

/-- All fixed powers of the cutoff and of a depth-linear sieve support fit
below one base power eventually. This retains a margin for arbitrarily
small fixed positive frequency savings elsewhere in the argument. -/
theorem eventually_height_pow_mul_support_le_base (k a b : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      height N k ^ a * SubpowerScale.z N k ^ (b * N) ≤ SubpowerScale.base N k := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_ge_atTop ((8 * a + b) * BPZScale.xExp k)] with N hN1 hN
  unfold height SubpowerScale.z SubpowerScale.base
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  have he : SubpowerScale.roughPower N k * (8 * N * a) +
      SubpowerScale.roughPower N k * (b * N) =
      ((8 * a + b) * BPZScale.xExp k) * N ^ (2 * k + 4) := by
    unfold SubpowerScale.roughPower
    rw [show 2 * k + 4 = (2 * k + 3) + 1 by omega, pow_succ]
    ring
  rw [he]
  calc
    _ ≤ N * N ^ (2 * k + 4) := Nat.mul_le_mul_right _ hN
    _ = SubpowerScale.scalePower N k := by
      unfold SubpowerScale.scalePower
      rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega, pow_succ]
      ring

/-- In particular any prescribed fixed power loss is below X eventually;
taking a multiple of k^201 gives an integral form of compatibility with the
convenient-moment saving, without introducing fractional powers. -/
theorem eventually_height_pow_mul_support_le_X {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      height N k ^ a * SubpowerScale.z N k ^ (b * N) ≤ SubpowerScale.X N k := by
  have hx : 1 ≤ BPZScale.xExp k := Nat.succ_le_of_lt (by unfold BPZScale.xExp; positivity)
  filter_upwards [eventually_height_pow_mul_support_le_base k a b] with N hN
  apply hN.trans
  change SubpowerScale.base N k ≤ SubpowerScale.base N k ^ BPZScale.xExp k
  simpa using Nat.pow_le_pow_right (show 1 ≤ SubpowerScale.base N k by
    unfold SubpowerScale.base
    exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))) hx

theorem eventually_const_le_base (k A : ℕ) :
    ∀ᶠ N : ℕ in atTop, A ≤ SubpowerScale.base N k := by
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop (1 : ℕ)] with N hA hN
  have hpow : N ≤ SubpowerScale.scalePower N k := by
    unfold SubpowerScale.scalePower
    simpa using Nat.pow_le_pow_right hN (by omega : 1 ≤ 2 * k + 5)
  exact hA.trans ((show N < 2 ^ N from Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) hpow))

/-- The cutoff lies inside the common integer frequency window for every
certificate in the original near-product range. -/
theorem eventually_four_mul_height_le_X (k B : ℕ) (hk : 0 < k) :
    ∀ᶠ N : ℕ in atTop, 4 * B * height N k ≤ SubpowerScale.X N k := by
  have hx : 2 ≤ BPZScale.xExp k := by
    have hpos : 0 < 3 ^ k * k ^ 100 := by positivity
    unfold BPZScale.xExp
    nlinarith
  filter_upwards [eventually_height_pow_mul_support_le_base k 1 0,
    eventually_const_le_base k (4 * B)] with N hH hB
  simp only [pow_one, zero_mul, pow_zero, mul_one] at hH
  calc
    _ ≤ SubpowerScale.base N k * SubpowerScale.base N k := Nat.mul_le_mul hB hH
    _ = SubpowerScale.base N k ^ 2 := by ring
    _ ≤ SubpowerScale.base N k ^ BPZScale.xExp k :=
      Nat.pow_le_pow_right (by unfold SubpowerScale.base; exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))) hx
    _ = SubpowerScale.X N k := rfl

theorem two_mul_height_lt_modulus {B X H V M v : ℕ}
    (_hB : 0 < B) (hM : 0 < M) (hv : 0 < v)
    (hwindow : X / 2 < B * V) (hHX : 4 * B * H ≤ X) :
    2 * H < M * V * v := by
  have hh : 2 * B * H ≤ X / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by nlinarith)
  have hHV : 2 * H < V := by nlinarith
  have hV : V ≤ M * V * v :=
    (Nat.le_mul_of_pos_left V hM).trans (Nat.le_mul_of_pos_right _ hv)
  exact hHV.trans_le hV

/-- Uniformly over all actual medium certificates and all positive residual
sieve moduli. In particular this applies to every squarefree gcd quotient. -/
theorem eventually_certificate_window {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (i : Fin S.k) (C : RefinedTupleCertificate S (SubpowerScale.X N S.k)),
        C ∈ MediumCertificateCover.certificates S (SubpowerScale.X N S.k)
          (SubpowerScale.z N S.k) (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) i →
        ∀ v : ℕ, 0 < v →
          2 * height N S.k < refinementModulus S * C.val.value * v := by
  classical
  filter_upwards [eventually_four_mul_height_le_X S.k B (by have := S.hk3; omega)]
    with N hH i C hC v hv
  exact two_mul_height_lt_modulus hB (refinementModulus_pos S) hv
    (Finset.mem_filter.mp hC).2.2.1 hH

def fixedBaseExponent (k : ℕ) : ℕ := Nat.log 2 k + 1

def tailExponent (N k : ℕ) : ℕ :=
  SubpowerScale.roughPower N k * (4 * N) + N ^ 2 + fixedBaseExponent k * (2 * N)

theorem tailExponent_add_self_le_heightExponent {N k : ℕ}
    (hN : 0 < N) (hk : 0 < k) (hlarge : 2 * fixedBaseExponent k + 1 ≤ N) :
    tailExponent N k + N ≤ SubpowerScale.roughPower N k * (8 * N) := by
  have hr := SubpowerScale.self_le_roughPower hN hk
  have hm := Nat.mul_le_mul_right N hlarge
  have hn := Nat.mul_le_mul_right (4 * N) hr
  unfold tailExponent
  nlinarith

noncomputable def tailScaleFactor {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  (SubpowerScale.z N S.k : ℝ) ^ (4 * N) * (S.k : ℝ) ^ (2 * N) /
    ((height N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k))

theorem tailScaleFactor_nonneg {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    0 ≤ tailScaleFactor S N := by
  unfold tailScaleFactor
  exact div_nonneg (by positivity) (mul_nonneg (by positivity) (refinedDensity_pos S _).le)

theorem eventually_tailScaleFactor_le_inv_pow {B K : ℕ} (S : BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop, tailScaleFactor S N ≤ 1 / (2 : ℝ) ^ N := by
  have hk : 0 < S.k := by have := S.hk3; omega
  filter_upwards [MediumEndpointDecay.eventually_one_le_pow_mul_refinedDensity S,
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop (2 * fixedBaseExponent S.k + 1)]
    with N hVrecip hN hlarge
  have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
  have hH : (0 : ℝ) < height N S.k := by exact_mod_cast height_pos N S.k
  have hkbase : (S.k : ℝ) ≤ (2 : ℝ) ^ fixedBaseExponent S.k := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) S.k).le
  have hkpow : (S.k : ℝ) ^ (2 * N) ≤ (2 : ℝ) ^ (fixedBaseExponent S.k * (2 * N)) := by
    calc
      _ ≤ ((2 : ℝ) ^ fixedBaseExponent S.k) ^ (2 * N) :=
        pow_le_pow_left₀ (by positivity) hkbase _
      _ = _ := (pow_mul _ _ _).symm
  let U : ℝ := (SubpowerScale.z N S.k : ℝ) ^ (4 * N) * (S.k : ℝ) ^ (2 * N)
  have hU : U * (2 : ℝ) ^ (N ^ 2) ≤ (2 : ℝ) ^ tailExponent N S.k := by
    calc
      _ ≤ (SubpowerScale.z N S.k : ℝ) ^ (4 * N) *
          (2 : ℝ) ^ (fixedBaseExponent S.k * (2 * N)) * (2 : ℝ) ^ (N ^ 2) := by
        dsimp [U]
        gcongr
      _ = _ := by
        simp only [SubpowerScale.z, Nat.cast_pow, Nat.cast_ofNat]
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        unfold tailExponent
        ring
  have hden : (2 : ℝ) ^ (tailExponent N S.k + N) ≤ height N S.k := by
    have he := tailExponent_add_self_le_heightExponent (by omega : 0 < N) hk hlarge
    have hn := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) he
    simpa [height, SubpowerScale.z, ← pow_mul] using (show
      ((2 ^ (tailExponent N S.k + N) : ℕ) : ℝ) ≤
        ((2 ^ (SubpowerScale.roughPower N S.k * (8 * N)) : ℕ) : ℝ) by exact_mod_cast hn)
  have hmain : U * (2 : ℝ) ^ N ≤ (height N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) := by
    calc
      _ ≤ (U * (2 : ℝ) ^ N) * ((2 : ℝ) ^ (N ^ 2) * refinedDensity S (SubpowerScale.z N S.k)) :=
        le_mul_of_one_le_right (by dsimp [U]; positivity) hVrecip
      _ = (U * (2 : ℝ) ^ (N ^ 2)) * (2 : ℝ) ^ N * refinedDensity S (SubpowerScale.z N S.k) := by ring
      _ ≤ (2 : ℝ) ^ tailExponent N S.k * (2 : ℝ) ^ N * refinedDensity S (SubpowerScale.z N S.k) := by gcongr
      _ ≤ _ := by rw [← pow_add]; exact mul_le_mul_of_nonneg_right hden hV.le
  unfold tailScaleFactor
  exact (div_le_div_iff₀ (mul_pos hH hV) (by positivity : (0 : ℝ) < (2 : ℝ)^N)).mpr
    (by simpa [U] using hmain)

noncomputable def normalizedTailEnvelope {B K : ℕ}
    (S : BPZSection6Input B K) (M N : ℕ) : ℝ :=
  ((S.k : ℝ) * M ^ 2 / 2) * (2 * (N : ℝ) + 1) *
    roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) ^ (S.k - 1) *
      tailScaleFactor S N

theorem totalTailEnvelope_div_sieveScale {B K : ℕ}
    (S : BPZSection6Input B K) {M : ℕ} (hM : 0 < M) (N : ℕ) :
    totalTailEnvelope S.k M (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (2 * N) (height N S.k) /
        ((SubpowerScale.X N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) / M) =
      normalizedTailEnvelope S M N := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hXR : (SubpowerScale.X N S.k : ℝ) ≠ 0 := by exact_mod_cast (SubpowerScale.X_pos N S.k).ne'
  have hVR := (refinedDensity_pos S (SubpowerScale.z N S.k)).ne'
  have hHR : (height N S.k : ℝ) ≠ 0 := by exact_mod_cast (height_pos N S.k).ne'
  unfold totalTailEnvelope normalizedTailEnvelope tailScaleFactor
  push_cast
  rw [show 2 * (2 * N) = 4 * N by omega]
  field_simp

theorem tendsto_normalizedTailEnvelope_zero {B K : ℕ}
    (S : BPZSection6Input B K) (M : ℕ) :
    Tendsto (normalizedTailEnvelope S M) atTop (𝓝 0) := by
  have hk : 0 < S.k := by have := S.hk3; omega
  obtain ⟨A, hA, hmass⟩ := exists_full_roughMass_quadratic_bound hk
  let C : ℝ := ((S.k : ℝ) * M ^ 2 / 2) * 3 * A ^ (S.k - 1)
  have hlim : Tendsto (fun N : ℕ => C * ((N : ℝ) ^ (2 * (S.k - 1) + 1) / (2 : ℝ)^N))
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt
      (2 * (S.k - 1) + 1) (by norm_num : (1 : ℝ) < 2)).const_mul C
  apply squeeze_zero' (g := fun N : ℕ => C * ((N : ℝ) ^ (2 * (S.k - 1) + 1) / (2 : ℝ)^N)) _ _ hlim
  · apply Filter.Eventually.of_forall
    intro N
    unfold normalizedTailEnvelope
    apply mul_nonneg _ (tailScaleFactor_nonneg S N)
    unfold roughReciprocalMass
    positivity
  · filter_upwards [eventually_tailScaleFactor_le_inv_pow S, eventually_ge_atTop (1 : ℕ)]
      with N hscale hN
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hR0 : 0 ≤ roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) := by
      unfold roughReciprocalMass
      positivity
    have hR := pow_le_pow_left₀ hR0 (hmass N (by omega)) (S.k - 1)
    unfold normalizedTailEnvelope
    calc
      _ ≤ ((S.k : ℝ) * M ^ 2 / 2) * (3 * (N : ℝ)) *
          (A * (N : ℝ)^2)^(S.k-1) * (1 / (2 : ℝ)^N) := by
        apply mul_le_mul
        · apply mul_le_mul
          · gcongr
            linarith
          · exact hR
          · positivity
          · positivity
        · exact hscale
        · exact tailScaleFactor_nonneg S N
        · positivity
      _ = _ := by dsimp [C]; rw [mul_pow, ← pow_mul, pow_succ]; ring

theorem tendsto_totalTailEnvelope_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) {M : ℕ} (hM : 0 < M) :
    Tendsto (fun N => totalTailEnvelope S.k M (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (2 * N) (height N S.k) /
        ((SubpowerScale.X N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) / M))
      atTop (𝓝 0) := by
  simpa only [totalTailEnvelope_div_sieveScale S hM] using tendsto_normalizedTailEnvelope_zero S M

/-- The actual signed mass-minus-truncation sum on the original scale,
with the depth and height fixed as specified above. -/
noncomputable def signedTail {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  ∑ i : Fin S.k,
    ∑ C ∈ MediumCertificateCover.certificates S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) i,
    ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
      MediumSignedMainTerm.coefficient (2 * N) T *
        (IntegerSieveResidues.residueMass (SubpowerScale.X N S.k) (∏ p ∈ T, p) S.k
          (MediumSieveSmoothing.integerClass C) -
        windowCertificatePartial i C (SubpowerScale.z N S.k) (SubpowerScale.medium N S.k)
          (SubpowerScale.large N S.k) (height N S.k) T)

/-- Decay of the actual signed truncation error, not merely of an envelope.
The only remaining finite Fourier contribution is the retained partial sum. -/
theorem tendsto_signedTail_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N => signedTail S N /
      ((SubpowerScale.X N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) /
        refinementModulus S)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := normalizedTailEnvelope S (refinementModulus S)) _ _
    (tendsto_normalizedTailEnvelope_zero S (refinementModulus S))
  · exact Filter.Eventually.of_forall (fun N => norm_nonneg _)
  · apply Filter.Eventually.of_forall
    intro N
    have hz : 1 ≤ SubpowerScale.z N S.k := (SubpowerScale.z_pos N S.k)
    have hM : (0 : ℝ) < refinementModulus S := by exact_mod_cast refinementModulus_pos S
    have hX : (0 : ℝ) < SubpowerScale.X N S.k := by exact_mod_cast SubpowerScale.X_pos N S.k
    have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
    have hden : 0 < (SubpowerScale.X N S.k : ℝ) *
        refinedDensity S (SubpowerScale.z N S.k) / refinementModulus S := by positivity
    have hf := abs_signed_mass_sub_windowPartial_le (S := S)
      (medium := SubpowerScale.medium N S.k) (large := SubpowerScale.large N S.k)
      (L := 2 * N) hB (SubpowerScale.X_pos N S.k) (height_pos N S.k) hz
    change |signedTail S N| ≤ _ at hf
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
    rw [← totalTailEnvelope_div_sieveScale S (refinementModulus_pos S) N]
    exact div_le_div_of_nonneg_right hf hden.le

end Erdos387Proof.MediumFourierTailDecay
