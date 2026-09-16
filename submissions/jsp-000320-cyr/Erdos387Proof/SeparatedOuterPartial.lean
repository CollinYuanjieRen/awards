import Erdos387Proof.SeparatedPartialBound
import Erdos387Proof.SeparatedTotalEnvelope
import Erdos387Proof.SeparatedParameterWindow

/-! Outer summation of the actual separated partial Fourier remainder.
The per-certificate bound of `SeparatedPartialBound` is summed over the
Brun prime subsets and over the `S.k` coordinates, and the resulting
constants are charged against `SeparatedTotalEnvelope.finiteEnvelope`. -/

set_option autoImplicit false

namespace Erdos387Proof.SeparatedOuterPartial

open Erdos387 Erdos387.CoverBPZ
open MediumFourierTailDecay MediumSubpowerReduction Filter
open scoped BigOperators Topology

/-- The inner dyadic-key envelope: the right-hand side of
`SeparatedOuterBound.sum_keys_envelope_le` on the subpower scale. -/
noncomputable def keysEnvelope {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  SeparatedOuterBound.envelopeConstant B * height N S.k *
    ((2*(SubpowerScale.X N S.k : ℝ))/Real.sqrt (SubpowerScale.base N S.k : ℝ)) *
    (1+Real.log (SubpowerScale.X N S.k : ℝ))^4 *
    (Nat.log2 (SubpowerScale.X N S.k)+1 : ℕ) *
    roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^S.k

theorem keysEnvelope_nonneg {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    0 ≤ keysEnvelope S N := by
  have hc := SeparatedOuterBound.envelopeConstant_nonneg B
  unfold keysEnvelope roughReciprocalMass
  positivity

/-- The frozen finite envelope factors exactly as
outer multiplicities times the inner key envelope. -/
theorem finiteEnvelope_eq {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    SeparatedTotalEnvelope.finiteEnvelope S N =
      (S.k : ℝ) * (((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N)) *
        (((SubpowerScale.z N S.k : ℝ)^(2*N)*(2*(height N S.k : ℝ))) * keysEnvelope S N)) := by
  unfold SeparatedTotalEnvelope.finiteEnvelope keysEnvelope
  ring

/-- The truncated Brun coefficient is a sign or zero. -/
theorem abs_coefficient_le_one (L : ℕ) (T : Finset ℕ) :
    |MediumSignedMainTerm.coefficient L T| ≤ 1 := by
  unfold MediumSignedMainTerm.coefficient
  split_ifs with h
  · simp [abs_pow]
  · simp

theorem eventually_abs_totalPartialRemainder_le {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      |SeparatedPartialFourier.totalPartialRemainder S N| ≤
        SeparatedTotalEnvelope.finiteEnvelope S N := by
  classical
  have hk : 0 < S.k := by have := S.hk3; omega
  filter_upwards [SeparatedParameterWindow.eventually_parameters S,
    SeparatedPartialFourier.eventually_certificate_window S hB,
    eventually_ge_atTop (2*BPZScale.xExp S.k)] with N hpar hwin hNx
  obtain ⟨hN0, hz, hkX, hzy, ht6, hM, hzbase, hH2, hHt⟩ := hpar
  have hXpos : 0 < SubpowerScale.X N S.k := SubpowerScale.X_pos N S.k
  have hbase : 1 ≤ SubpowerScale.base N S.k := by
    unfold SubpowerScale.base; exact Nat.one_le_pow _ _ (by norm_num)
  have hHpos : 1 ≤ height N S.k := by omega
  have hz1 : 1 ≤ SubpowerScale.z N S.k := by omega
  have hkz : S.k ≤ SubpowerScale.z N S.k := by omega
  have hyX : BPZScale.y (SubpowerScale.base N S.k) S.k ≤ SubpowerScale.X N S.k :=
    SeparatedParameterWindow.y_le_X N hk
  have hE := keysEnvelope_nonneg S N
  -- the inner key sum is bounded by `keysEnvelope`
  have hkeys : ∀ i : Fin S.k,
      (∑ c ∈ (SeparatedPrimeFibre.keys S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
          (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i).attach,
        SeparatedFibreBound.envelope B S.k (SubpowerScale.base N S.k) (height N S.k)
          (SeparatedCertificateEnlargement.blockUpper
            (SeparatedPrimeFibre.representative c).2.2)) ≤ keysEnvelope S N := by
    intro i
    exact SeparatedOuterBound.sum_keys_envelope_le (X := SubpowerScale.X N S.k)
      (z := SubpowerScale.z N S.k) (t := SubpowerScale.base N S.k)
      (medium := SubpowerScale.medium N S.k) (second := SubpowerScale.secondMin N S.k)
      (gap := SubpowerScale.gap N S.k) (H := height N S.k) S i hbase hHpos hXpos hyX
  have hkeysnn : ∀ i : Fin S.k,
      (0 : ℝ) ≤ ∑ c ∈ (SeparatedPrimeFibre.keys S (SubpowerScale.X N S.k)
          (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
          (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i).attach,
        SeparatedFibreBound.envelope B S.k (SubpowerScale.base N S.k) (height N S.k)
          (SeparatedCertificateEnlargement.blockUpper
            (SeparatedPrimeFibre.representative c).2.2) := by
    intro i
    exact Finset.sum_nonneg fun c _ =>
      SeparatedFibreBound.envelope_nonneg _ _ _ _ _ (by omega)
  -- the per-subset bound
  have hterm : ∀ i : Fin S.k,
      ∀ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
      T.card ≤ 2*N →
      |∑ a ∈ SeparatedCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
          (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
          (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i,
        ConvenientPartialFourier.partialRemainder i a (SubpowerScale.z N S.k) 0
          (SubpowerScale.medium N S.k) (height N S.k) T| ≤
        ((SubpowerScale.z N S.k : ℝ)^(2*N)*(2*(height N S.k : ℝ))) * keysEnvelope S N := by
    intro i T hT hTcard
    have hsub := Finset.mem_powerset.mp hT
    have hprime : ∀ p ∈ T, p.Prime := fun p hp =>
      (MediumSieveEuler.mem_windowPrimes.mp (hsub hp)).1
    have hgpos : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp => (hprime p hp).pos
    have hgt : (∏ p ∈ T, p) ≤ SubpowerScale.base N S.k :=
      SeparatedCertificatePhase.brun_support_le_base N S.k T hNx hTcard
        (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp (hsub hp)).2.2)
    have hwindow : ∀ a ∈ SeparatedCertificateEnlargement.certificates S
        (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
        (SubpowerScale.medium N S.k) (SubpowerScale.secondMin N S.k)
        (SubpowerScale.gap N S.k) i,
        2*height N S.k < refinementModulus S * a.1.val.value * (∏ p ∈ T, p) :=
      fun a ha => hwin i a ha _ hgpos
    have h1 := SeparatedPartialBound.abs_sum_certificate_partial_le
      (X := SubpowerScale.X N S.k) (z := SubpowerScale.z N S.k)
      (t := SubpowerScale.base N S.k) (medium := SubpowerScale.medium N S.k)
      (H := height N S.k) (S := S) i hT hB hXpos hkX hz hzy ht6 hgt hM hH2 hHt hwindow
    refine h1.trans ?_
    have hlarge : ∀ p ∈ (∏ p ∈ T, p).primeFactors, S.k < p := by
      rw [Nat.primeFactors_prod hprime]
      intro p hp
      have := (MediumSieveEuler.mem_windowPrimes.mp (hsub hp)).2.1
      omega
    have hres : (localAssignmentResidues (∏ p ∈ T, p) S.k).card ≤
        SubpowerScale.z N S.k ^ (2*N) := by
      rw [card_localAssignmentResidues hlarge, Nat.primeFactors_prod hprime]
      exact (Nat.pow_le_pow_left hkz _).trans' (Nat.pow_le_pow_right hk hTcard)
    have hcast : (((localAssignmentResidues (∏ p ∈ T, p) S.k).card*(2*height N S.k) : ℕ) : ℝ) ≤
        (SubpowerScale.z N S.k : ℝ)^(2*N)*(2*(height N S.k : ℝ)) := by
      have hnat : (localAssignmentResidues (∏ p ∈ T, p) S.k).card*(2*height N S.k) ≤
          SubpowerScale.z N S.k ^ (2*N)*(2*height N S.k) :=
        Nat.mul_le_mul_right _ hres
      calc (((localAssignmentResidues (∏ p ∈ T, p) S.k).card*(2*height N S.k) : ℕ) : ℝ)
          ≤ ((SubpowerScale.z N S.k ^ (2*N)*(2*height N S.k) : ℕ) : ℝ) := by
            exact_mod_cast hnat
        _ = _ := by push_cast; ring
    exact mul_le_mul hcast (hkeys i) (hkeysnn i) (by positivity)
  -- sum over the Brun subsets
  have hPz : MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k) ⊆
      Finset.range (SubpowerScale.z N S.k) := fun p hp =>
    Finset.mem_range.mpr (MediumSieveEuler.mem_windowPrimes.mp hp).2.2
  have hinner : ∀ i : Fin S.k,
      |∑ a ∈ SeparatedCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
          (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
          (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i,
        ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
          MediumSignedMainTerm.coefficient (2*N) T *
            ConvenientPartialFourier.partialRemainder i a (SubpowerScale.z N S.k) 0
              (SubpowerScale.medium N S.k) (height N S.k) T| ≤
        ((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N)) *
          (((SubpowerScale.z N S.k : ℝ)^(2*N)*(2*(height N S.k : ℝ))) * keysEnvelope S N) := by
    intro i
    have hcomm : (∑ a ∈ SeparatedCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
          (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
          (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i,
        ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
          MediumSignedMainTerm.coefficient (2*N) T *
            ConvenientPartialFourier.partialRemainder i a (SubpowerScale.z N S.k) 0
              (SubpowerScale.medium N S.k) (height N S.k) T) =
        ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
          MediumSignedMainTerm.coefficient (2*N) T *
            ∑ a ∈ SeparatedCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
              (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
              (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i,
            ConvenientPartialFourier.partialRemainder i a (SubpowerScale.z N S.k) 0
              (SubpowerScale.medium N S.k) (height N S.k) T := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun T _ => by rw [Finset.mul_sum]
    rw [hcomm]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hzero : ∀ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
        T ∉ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset.filter
          (fun T => T.card ≤ 2*N) →
        |MediumSignedMainTerm.coefficient (2*N) T *
          ∑ a ∈ SeparatedCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
            (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
            (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i,
          ConvenientPartialFourier.partialRemainder i a (SubpowerScale.z N S.k) 0
            (SubpowerScale.medium N S.k) (height N S.k) T| = 0 := by
      intro T hT hnot
      have hTc : ¬ T.card ≤ 2*N := by
        intro hc
        exact hnot (Finset.mem_filter.mpr ⟨hT, hc⟩)
      simp [MediumSignedMainTerm.coefficient, hTc]
    rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero]
    calc
      _ ≤ ∑ _T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset.filter
            (fun T => T.card ≤ 2*N),
          ((SubpowerScale.z N S.k : ℝ)^(2*N)*(2*(height N S.k : ℝ))) * keysEnvelope S N := by
        refine Finset.sum_le_sum fun T hT => ?_
        obtain ⟨hTP, hTL⟩ := Finset.mem_filter.mp hT
        rw [abs_mul]
        calc |MediumSignedMainTerm.coefficient (2*N) T| * |∑ a ∈ _, _|
            ≤ 1 * |∑ a ∈ SeparatedCertificateEnlargement.certificates S
                (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) (SubpowerScale.y N S.k)
                (SubpowerScale.medium N S.k) (SubpowerScale.secondMin N S.k)
                (SubpowerScale.gap N S.k) i,
              ConvenientPartialFourier.partialRemainder i a (SubpowerScale.z N S.k) 0
                (SubpowerScale.medium N S.k) (height N S.k) T| :=
              mul_le_mul_of_nonneg_right (abs_coefficient_le_one _ _) (abs_nonneg _)
          _ = _ := one_mul _
          _ ≤ _ := hterm i T hTP hTL
      _ = (((MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset.filter
            (fun T => T.card ≤ 2*N)).card : ℝ) *
          (((SubpowerScale.z N S.k : ℝ)^(2*N)*(2*(height N S.k : ℝ))) * keysEnvelope S N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N)) *
          (((SubpowerScale.z N S.k : ℝ)^(2*N)*(2*(height N S.k : ℝ))) * keysEnvelope S N) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hc := MediumEndpointError.card_truncated_powerset_le (L := 2*N) hPz hz1
        have : ((((MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset.filter
            (fun T => T.card ≤ 2*N)).card : ℝ)) ≤
            (((2*N+1)*SubpowerScale.z N S.k^(2*N) : ℕ) : ℝ) := by exact_mod_cast hc
        refine this.trans ?_
        push_cast
        ring_nf
        exact le_rfl
  calc |SeparatedPartialFourier.totalPartialRemainder S N|
      ≤ ∑ i : Fin S.k,
        |∑ a ∈ SeparatedCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
            (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
            (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i,
          ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
            MediumSignedMainTerm.coefficient (2*N) T *
              ConvenientPartialFourier.partialRemainder i a (SubpowerScale.z N S.k) 0
                (SubpowerScale.medium N S.k) (height N S.k) T| := by
        rw [SeparatedPartialFourier.totalPartialRemainder]
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin S.k, ((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N)) *
          (((SubpowerScale.z N S.k : ℝ)^(2*N)*(2*(height N S.k : ℝ))) * keysEnvelope S N) :=
        Finset.sum_le_sum fun i _ => hinner i
    _ = (S.k : ℝ) * (((2*(N : ℝ)+1)*(SubpowerScale.z N S.k : ℝ)^(2*N)) *
          (((SubpowerScale.z N S.k : ℝ)^(2*N)*(2*(height N S.k : ℝ))) * keysEnvelope S N)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = SeparatedTotalEnvelope.finiteEnvelope S N := (finiteEnvelope_eq S N).symm

end Erdos387Proof.SeparatedOuterPartial
