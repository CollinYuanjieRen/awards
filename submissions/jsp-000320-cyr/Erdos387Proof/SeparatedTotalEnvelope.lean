import Erdos387Proof.SeparatedOuterBound
import Erdos387Proof.SeparatedOscillatoryDecay
import Erdos387Proof.MediumSubpowerReduction

/-! The completely counted separated nonzero Fourier envelope tends to
zero on the same refined sieve scale as the original candidate count. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedTotalEnvelope
open Erdos387 Erdos387.CoverBPZ MediumFourierTailDecay MediumMainTermDecay
open MediumSubpowerReduction SeparatedOuterBound Filter
open scoped Topology

noncomputable def finiteEnvelope {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  S.k*(2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N)*
    ((SubpowerScale.z N S.k : ℝ)^(2*N)*(2*height N S.k)) *
    envelopeConstant B*height N S.k*((2*(SubpowerScale.X N S.k : ℝ))/
      Real.sqrt (SubpowerScale.base N S.k : ℝ))*
    (1+Real.log (SubpowerScale.X N S.k : ℝ))^4*
    (Nat.log2 (SubpowerScale.X N S.k)+1 : ℕ)*
    roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^S.k

theorem finiteEnvelope_nonneg {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    0≤finiteEnvelope S N := by
  have hc := envelopeConstant_nonneg B
  unfold finiteEnvelope roughReciprocalMass
  positivity

theorem finiteEnvelope_div_sieveScale_le {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    finiteEnvelope S N/sieveScale S N≤
      (8*S.k*envelopeConstant B*refinementModulus S*(1/Real.log 2+1))*
        SeparatedOscillatoryDecay.normalizedEnvelope S 2 2 0 0 5 1 S.k N := by
  have hM : (refinementModulus S : ℝ)≠0 := by exact_mod_cast (refinementModulus_pos S).ne'
  have hX : (SubpowerScale.X N S.k : ℝ)≠0 := by exact_mod_cast (SubpowerScale.X_pos N S.k).ne'
  have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
  have hc := envelopeConstant_nonneg B
  have hlog2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hR : 0≤roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) := by
    unfold roughReciprocalMass; positivity
  have hL : 0≤1+Real.log (SubpowerScale.X N S.k : ℝ) := by positivity
  let A : ℝ := ((MediumOscillatoryDecay.loss 2 2 0 0 N S.k : ℝ)/
    refinedDensity S (SubpowerScale.z N S.k))/Real.sqrt (SubpowerScale.base N S.k : ℝ)
  have hA : 0≤A := by dsimp [A]; positivity
  have heq : finiteEnvelope S N/sieveScale S N=
      (4*S.k*envelopeConstant B*refinementModulus S)*(2*(N : ℝ)+1)*A*
        (1+Real.log (SubpowerScale.X N S.k : ℝ))^4*
        (Nat.log2 (SubpowerScale.X N S.k)+1 : ℕ)*
        roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^S.k := by
    unfold finiteEnvelope sieveScale
    dsimp [A,MediumOscillatoryDecay.loss]
    push_cast
    simp only [zero_mul,pow_zero,mul_one]
    rw [show 2*2*N=2*N+2*N by omega,pow_add]
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ (4*S.k*envelopeConstant B*refinementModulus S)*(2*((N : ℝ)+1))*A*
        (1+Real.log (SubpowerScale.X N S.k : ℝ))^4*
        ((1/Real.log 2+1)*(1+Real.log (SubpowerScale.X N S.k : ℝ)))*
        roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^S.k := by
      gcongr
      · linarith
      · exact SeparatedRoughBound.log2_add_one_le _
    _ = _ := by
      unfold SeparatedOscillatoryDecay.normalizedEnvelope
      dsimp [A]
      ring

theorem tendsto_finiteEnvelope_div_sieveScale_zero {B K : ℕ} (S : BPZSection6Input B K) :
    Tendsto (fun N => finiteEnvelope S N/sieveScale S N) atTop (𝓝 0) := by
  have hlim := (SeparatedOscillatoryDecay.tendsto_normalizedEnvelope_zero S 2 2 0 0 5 1 S.k).const_mul
    (8*S.k*envelopeConstant B*refinementModulus S*(1/Real.log 2+1))
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall (fun N => div_nonneg
      (finiteEnvelope_nonneg S N) (sieveScale_pos S N).le)
  · exact Filter.Eventually.of_forall (finiteEnvelope_div_sieveScale_le S)

end Erdos387Proof.SeparatedTotalEnvelope
