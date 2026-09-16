import Erdos387Proof.ConvenientFourierTail
import Erdos387Proof.ConvenientMainDecay
import Erdos387Proof.MediumSubpowerReduction
import Erdos387Proof.MediumFourierTailDecay

/-! The complete convenient Fourier tail tends to zero after normalization
by the original refined sieve scale. The prime-counting constant is chosen
from its unconditional theorem inside the actual-tail result. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientFourierTailDecay
open Erdos387 Erdos387.CoverBPZ ConvenientFourierTail
open MediumFourierTailDecay MediumMainTermDecay MediumSubpowerReduction Filter
open scoped BigOperators Topology

noncomputable def normalizedTailEnvelope {B K : ℕ}
    (S : BPZSection6Input B K) (C : ℝ) (N : ℕ) : ℝ :=
  (3*S.k*B*C*(refinementModulus S : ℝ)^2)*(2*(N : ℝ)+1)*
    (roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^(S.k+1)/
      Real.log (SubpowerScale.z N S.k : ℝ))*tailScaleFactor S N

theorem totalTailEnvelope_div_sieveScale {B K : ℕ}
    (S : BPZSection6Input B K) (C : ℝ) (N : ℕ) :
    ConvenientFourierTail.totalTailEnvelope S.k (refinementModulus S) B
      (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) (2*N) (height N S.k) C /
      sieveScale S N=normalizedTailEnvelope S C N := by
  have hM : (refinementModulus S : ℝ)≠0 := by exact_mod_cast (refinementModulus_pos S).ne'
  have hX : (SubpowerScale.X N S.k : ℝ)≠0 := by exact_mod_cast (SubpowerScale.X_pos N S.k).ne'
  have hV := (refinedDensity_pos S (SubpowerScale.z N S.k)).ne'
  have hH : (height N S.k : ℝ)≠0 := by exact_mod_cast (height_pos N S.k).ne'
  unfold ConvenientFourierTail.totalTailEnvelope normalizedTailEnvelope sieveScale tailScaleFactor
  push_cast
  rw [show 4*N=2*N+2*N by omega,pow_add]
  field_simp
  ring

theorem tendsto_normalizedTailEnvelope_zero {B K : ℕ}
    (S : BPZSection6Input B K) {C : ℝ} (hC : 0≤C) :
    Tendsto (normalizedTailEnvelope S C) atTop (𝓝 0) := by
  have hk : 0<S.k := by have := S.hk3; omega
  obtain ⟨A,hA,hmass⟩ := ConvenientMainDecay.exists_roughMass_pow_div_log_le_inv hk
  let F : ℝ := 3*S.k*B*C*(refinementModulus S : ℝ)^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hlim : Tendsto (fun N : ℕ => (F*3*A)*((1 : ℝ)/(2 : ℝ)^N)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 0
      (by norm_num : (1 : ℝ)<2)).const_mul (F*3*A)
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hlog : 0<Real.log (SubpowerScale.z N S.k : ℝ) := Real.log_pos (by
      exact_mod_cast (show 1<SubpowerScale.z N S.k from
        lt_of_lt_of_le (by omega) (SubpowerScale.two_le_z (by omega) hk)))
    unfold normalizedTailEnvelope
    apply mul_nonneg _ (tailScaleFactor_nonneg S N)
    unfold roughReciprocalMass
    positivity
  · filter_upwards [eventually_tailScaleFactor_le_inv_pow S,
      eventually_ge_atTop (1 : ℕ)] with N htail hN
    have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
    have hmassN := hmass N (by omega)
    have hm : (2*(N : ℝ)+1)*
        (roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^(S.k+1)/
          Real.log (SubpowerScale.z N S.k : ℝ)) ≤ 3*A := by
      apply (mul_le_mul_of_nonneg_left hmassN (by positivity : 0≤2*(N : ℝ)+1)).trans
      have hNpos : (0 : ℝ)<N := by linarith
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hNpos).mpr
      nlinarith
    unfold normalizedTailEnvelope
    change F*(2*(N : ℝ)+1)*_*_≤_
    rw [mul_assoc F]
    calc
      _ ≤ (F*(3*A))*tailScaleFactor S N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hF)
          (tailScaleFactor_nonneg S N)
      _ ≤ (F*(3*A))*((1 : ℝ)/(2 : ℝ)^N) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring

noncomputable def signedTail {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  ∑ i : Fin S.k,
    ∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i,
    ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
      MediumSignedMainTerm.coefficient (2*N) T *
        (IntegerSieveResidues.residueMass (SubpowerScale.X N S.k) (∏ p ∈ T,p) S.k
          (MediumSieveSmoothing.integerClass t.1) -
        ConvenientFourierTail.windowCertificatePartial i t (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (height N S.k) T)

theorem tendsto_signedTail_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0<B) :
    Tendsto (fun N => signedTail S N/sieveScale S N) atTop (𝓝 0) := by
  obtain ⟨C,hC,hcheb⟩ := PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  have hk : 0<S.k := by have := S.hk3; omega
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => norm_nonneg _)) ?_
    (tendsto_normalizedTailEnvelope_zero S hC.le)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hz := SubpowerScale.two_le_z (by omega : 0<N) hk
  have hy : 0<SubpowerScale.y N S.k := by
    unfold SubpowerScale.y BPZScale.y SubpowerScale.base
    positivity
  have ht := ConvenientFourierTail.abs_signed_mass_sub_windowPartial_le (S := S)
    (medium := SubpowerScale.medium N S.k) (L := 2*N)
    hC hcheb hz hz hB (SubpowerScale.X_pos N S.k) (height_pos N S.k) hy
  change |signedTail S N|≤_ at ht
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (sieveScale_pos S N)]
  rw [← totalTailEnvelope_div_sieveScale S C N]
  exact div_le_div_of_nonneg_right ht (sieveScale_pos S N).le

end Erdos387Proof.ConvenientFourierTailDecay
