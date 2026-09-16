import Erdos387Proof.SeparatedFourierTail
import Erdos387Proof.ConvenientFourierTailDecay

/-! Actual separated Fourier-tail decay. The finite envelope is the same
fully counted reciprocal-mass expression already treated for convenient
certificates; the summation domain here is the actual separated family. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedFourierTailDecay
open Erdos387 Erdos387.CoverBPZ SeparatedFourierTail
open MediumFourierTailDecay MediumSubpowerReduction Filter
open scoped BigOperators Topology

noncomputable def signedTail {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  ∑ i : Fin S.k,
    ∑ t∈SeparatedCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
      (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i,
    ∑ T∈(MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
      MediumSignedMainTerm.coefficient (2*N) T*
        (IntegerSieveResidues.residueMass (SubpowerScale.X N S.k) (∏ p∈T,p) S.k
          (MediumSieveSmoothing.integerClass t.1)-
        windowCertificatePartial i t (SubpowerScale.z N S.k)
          (SubpowerScale.medium N S.k) (height N S.k) T)

theorem tendsto_signedTail_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0<B) :
    Tendsto (fun N => signedTail S N/sieveScale S N) atTop (𝓝 0) := by
  obtain ⟨C,hC,hcheb⟩ := PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  have hk : 0<S.k := by have := S.hk3; omega
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => norm_nonneg _)) ?_
    (ConvenientFourierTailDecay.tendsto_normalizedTailEnvelope_zero S hC.le)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hz : 2≤SubpowerScale.z N S.k := SubpowerScale.two_le_z (by omega) hk
  have ht := abs_signed_mass_sub_windowPartial_le (S := S)
    (y := SubpowerScale.y N S.k) (medium := SubpowerScale.medium N S.k)
    (second := SubpowerScale.secondMin N S.k) (gap := SubpowerScale.gap N S.k) (L := 2*N)
    hC hcheb hz hz hB (SubpowerScale.X_pos N S.k) (height_pos N S.k)
  change |signedTail S N|≤_ at ht
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (sieveScale_pos S N)]
  rw [← ConvenientFourierTailDecay.totalTailEnvelope_div_sieveScale S C N]
  exact div_le_div_of_nonneg_right ht (sieveScale_pos S N).le

end Erdos387Proof.SeparatedFourierTailDecay
