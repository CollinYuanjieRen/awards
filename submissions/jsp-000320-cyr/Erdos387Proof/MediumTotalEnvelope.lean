import Erdos387Proof.MediumOscillatoryDecay

/-! The explicit finite multiplicity/variation/completion budget and its
actual subpower-scale decay. Bounding the Fourier count by this budget is
a separate finite aggregation; no count estimate is a premise here. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumTotalEnvelope

open Erdos387 Erdos387.CoverBPZ MediumOscillatoryDecay MediumMainTermDecay
open Filter
open scoped Topology

noncomputable def budget (B k M X z L W H : ℕ) : ℝ :=
  (k : ℝ) * (((L : ℝ) + 1) * (z : ℝ)^L * 2^L * (k : ℝ)^L * (2 * H)) *
    ((48 * B + 4608 * H * (B : ℝ)^2) *
      (Real.log ((M : ℝ) * X * (z : ℝ)^L) + 1) *
      4^(W+L) * (z : ℝ)^L * H * M)

noncomputable def totalEnvelope {B K : ℕ} (S : BPZSection6Input B K)
    (X z medium large L W H : ℕ) : ℝ :=
  budget B S.k (refinementModulus S) X z L W H *
    MediumOscillatoryMass.envelope S X z medium large

noncomputable def constant {B K : ℕ} (S : BPZSection6Input B K) : ℝ :=
  4 * S.k * refinementModulus S * (48 * B + 4608 * (B : ℝ)^2) *
    (Real.log (refinementModulus S : ℝ) + 3)

theorem constant_nonneg {B K : ℕ} (S : BPZSection6Input B K) :
    0 ≤ constant S := by unfold constant; positivity

theorem budget_nonneg {B k M X z L W H : ℕ}
    (hM : 0 < M) (hX : 0 < X) (hz : 0 < z) :
    0 ≤ budget B k M X z L W H := by
  have hprod : (1 : ℝ) ≤ (M : ℝ) * X * (z : ℝ)^L := by
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hMR hXR) (one_le_pow₀ hzR)
  have hlog := Real.log_nonneg hprod
  unfold budget
  positivity

theorem eventually_budget_le {B K : ℕ} (S : BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop,
      budget B S.k (refinementModulus S) (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k) (2*N) (N^2) (MediumFourierTailDecay.height N S.k) ≤
      constant S * (loss 3 2 8 2 N S.k : ℝ) * ((N : ℝ)+1) *
        (1 + Real.log (SubpowerScale.X N S.k : ℝ)) := by
  have hk : 0 < S.k := by have := S.hk3; omega
  filter_upwards [MediumFourierTailDecay.eventually_height_pow_mul_support_le_X hk 0 2,
    eventually_ge_atTop (1 : ℕ)] with N hG hN
  simp only [pow_zero, one_mul] at hG
  let X := SubpowerScale.X N S.k
  let z := SubpowerScale.z N S.k
  let H := MediumFourierTailDecay.height N S.k
  let M := refinementModulus S
  have hX : (0 : ℝ) < X := by exact_mod_cast SubpowerScale.X_pos N S.k
  have hz : (0 : ℝ) < z := by exact_mod_cast SubpowerScale.z_pos N S.k
  have hM : (0 : ℝ) < M := by exact_mod_cast refinementModulus_pos S
  have hH1 : (1 : ℝ) ≤ H := by
    exact_mod_cast MediumFourierTailDecay.height_pos N S.k
  have hGreal : (z : ℝ)^(2*N) ≤ X := by exact_mod_cast hG
  have hLX : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hLM : 0 ≤ Real.log (M : ℝ) := Real.log_natCast_nonneg M
  have hlog : Real.log ((M : ℝ) * X * (z : ℝ)^(2*N)) + 1 ≤
      (Real.log (M : ℝ)+3) * (1 + Real.log (X : ℝ)) := by
    rw [Real.log_mul (mul_ne_zero hM.ne' hX.ne') (pow_ne_zero _ hz.ne'),
      Real.log_mul hM.ne' hX.ne']
    have hglog := Real.log_le_log (pow_pos hz _) hGreal
    nlinarith [mul_nonneg hLM hLX]
  have hlog0 : 0 ≤ Real.log ((M : ℝ) * X * (z : ℝ)^(2*N)) + 1 := by
    have hMX : (1 : ℝ) ≤ (M : ℝ)*X*(z : ℝ)^(2*N) := by
      apply one_le_mul_of_one_le_of_one_le
      · apply one_le_mul_of_one_le_of_one_le
        · dsimp [M]; exact_mod_cast refinementModulus_pos S
        · dsimp [X]; exact_mod_cast SubpowerScale.X_pos N S.k
      · apply one_le_pow₀
        exact_mod_cast SubpowerScale.z_pos N S.k
    linarith [Real.log_nonneg hMX]
  have hvar : 48 * (B : ℝ) + 4608 * H * (B : ℝ)^2 ≤
      (48 * B + 4608 * (B : ℝ)^2) * H := by
    nlinarith [mul_le_mul_of_nonneg_left hH1 (show (0:ℝ) ≤ 48*B by positivity)]
  have hdepth : ((2*N : ℕ) : ℝ) + 1 ≤ 2*((N : ℝ)+1) := by push_cast; linarith
  have hn : N ≤ N^2 := by
    simpa using Nat.pow_le_pow_right hN (by norm_num : 1 ≤ 2)
  have he : 2*N + 2*(N^2+2*N) ≤ 8*N^2 := by omega
  have htwo : (2 : ℝ)^(2*N) * 4^(N^2+2*N) ≤ (2 : ℝ)^(8*N^2) := by
    rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) he
  change budget B S.k M X z (2*N) (N^2) H ≤ _
  calc
    _ = (2 * S.k * (M : ℝ)) * (((2*N : ℕ) : ℝ)+1) *
        (z : ℝ)^(4*N) * ((2 : ℝ)^(2*N) * 4^(N^2+2*N)) *
        (S.k : ℝ)^(2*N) * (H : ℝ)^2 *
        (48*B+4608*H*(B : ℝ)^2) *
        (Real.log ((M : ℝ)*X*(z : ℝ)^(2*N))+1) := by
      unfold budget
      rw [show 4*N = 2*N+2*N by omega, pow_add]
      ring
    _ ≤ (2 * S.k * (M : ℝ)) * (2*((N : ℝ)+1)) *
        (z : ℝ)^(4*N) * (2 : ℝ)^(8*N^2) *
        (S.k : ℝ)^(2*N) * (H : ℝ)^2 *
        ((48*B+4608*(B : ℝ)^2)*H) *
        ((Real.log (M : ℝ)+3)*(1+Real.log (X : ℝ))) := by
      gcongr
    _ = _ := by
      simp only [constant, loss, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      change _ = (4 * S.k * (M : ℝ) * (48*B+4608*(B : ℝ)^2) *
        (Real.log (M : ℝ)+3)) *
        ((H : ℝ)^3 * (z : ℝ)^(2*2*N) * (2 : ℝ)^(8*N^2) * (S.k : ℝ)^(2*N)) *
        ((N : ℝ)+1) * (1+Real.log (X : ℝ))
      norm_num only [show 2*2*N=4*N by omega]
      ring

noncomputable def normalizedTotal {B K : ℕ} (S : BPZSection6Input B K)
    (N : ℕ) : ℝ :=
  totalEnvelope S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
    (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k)
    (2*N) (N^2) (MediumFourierTailDecay.height N S.k) /
      ((SubpowerScale.X N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k) /
        refinementModulus S)

theorem tendsto_normalizedTotal_zero {B K : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) : Tendsto (normalizedTotal S) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N => constant S * normalizedEnvelope S 3 2 8 2 1 1 N)
      atTop (𝓝 0) := by
    simpa using (tendsto_normalizedEnvelope_zero S hB 3 2 8 2 1 1).const_mul (constant S)
  apply squeeze_zero' _ _ hlim
  · apply Filter.Eventually.of_forall
    intro N
    have hb := budget_nonneg (B := B) (k := S.k) (L := 2*N) (W := N^2)
      (H := MediumFourierTailDecay.height N S.k) (refinementModulus_pos S)
      (SubpowerScale.X_pos N S.k) (SubpowerScale.z_pos N S.k)
    have he := envelope_nonneg S N
    have hv := refinedDensity_pos S (SubpowerScale.z N S.k)
    unfold normalizedTotal totalEnvelope
    positivity
  · filter_upwards [eventually_budget_le S] with N hb
    have he := envelope_nonneg S N
    have hv := refinedDensity_pos S (SubpowerScale.z N S.k)
    have hx : (0 : ℝ) < SubpowerScale.X N S.k := by exact_mod_cast SubpowerScale.X_pos N S.k
    have hm : (0 : ℝ) < refinementModulus S := by exact_mod_cast refinementModulus_pos S
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb he)
      (show 0 ≤ (SubpowerScale.X N S.k : ℝ)*refinedDensity S (SubpowerScale.z N S.k)/refinementModulus S by positivity)
    simpa only [normalizedTotal, totalEnvelope, normalizedEnvelope, pow_one, mul_div_assoc,
      mul_assoc] using h

end Erdos387Proof.MediumTotalEnvelope
