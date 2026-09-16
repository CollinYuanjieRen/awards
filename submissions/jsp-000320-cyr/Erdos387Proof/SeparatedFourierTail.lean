import Erdos387Proof.SeparatedMainMass
import Erdos387Proof.ConvenientFourierTail

/-! The complete finite Fourier tail on the actual separated-error enlarged
certificate family. All distinguished indices and split certificates remain
in the sum; compatibility is inherited through the proved generic inclusion. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedFourierTail
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open SeparatedMainMass IntegerSieveResidues MediumSieveSmoothing
open ConvenientFourierTail (certificateTailBound certificateTailBound_le)
open scoped BigOperators

noncomputable abbrev Certificates {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium second gap : ℕ) (i : Fin S.k) :=
  SeparatedCertificateEnlargement.certificates S X z y medium second gap i

noncomputable def windowCertificatePartial {B K X : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (t : SplitCertificate S X) (z medium H : ℕ) (T : Finset ℕ) : ℝ :=
  ConvenientFourierTail.windowCertificatePartial i t z 0 medium H T

theorem abs_certificateMass_sub_partial_le {B K X z y medium second gap H : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X} {T : Finset ℕ}
    (hX : 0<X) (hH : 0<H) (ht : t∈Certificates S X z y medium second gap i)
    (hT : T∈(MediumSieveEuler.windowPrimes S.k z).powerset) :
    |residueMass X (∏ p∈T,p) S.k (integerClass t.1)-
      windowCertificatePartial i t z medium H T|≤certificateTailBound t (∏ p∈T,p) H :=
  ConvenientFourierTail.abs_certificateMass_sub_partial_le hX hH
    (SeparatedCertificateEnlargement.mem_generic_split_enlargement ht) hT

/-- Rigorous certificate count obtained from the reciprocal-mass estimate:
every actual certificate has positive value at most `X`. -/
theorem card_certificates_le
    {B K X z y medium second gap : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) {C : ℝ} {N : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B) (hX : 0 < X)
    :
    ((Certificates S X z y medium second gap i).card : ℝ) ≤
      (X : ℝ) * ((6 * B * C / Real.log z) *
        roughReciprocalMass z X ^ (S.k + 1)) := by
  classical
  calc
    _ = ∑ t ∈ Certificates S X z y medium second gap i, (1 : ℝ) := by simp
    _ ≤ ∑ t ∈ Certificates S X z y medium second gap i,
        (X : ℝ) * ((1 : ℝ) / t.1.val.value) := by
      apply Finset.sum_le_sum
      intro t ht
      have hval := (SeparatedCertificateEnlargement.admissible ht).upper
      have hv : (0 : ℝ) < t.1.val.value := by exact_mod_cast t.1.val.value_pos
      calc
        (1 : ℝ) = (t.1.val.value : ℝ) / t.1.val.value := by field_simp
        _ ≤ (X : ℝ) / t.1.val.value :=
          div_le_div_of_nonneg_right (by exact_mod_cast hval) hv.le
        _ = (X : ℝ) * ((1 : ℝ) / t.1.val.value) := by ring
    _ = (X : ℝ) *
        (∑ t ∈ Certificates S X z y medium second gap i,
          (1 : ℝ) / t.1.val.value) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_certificates_reciprocal_le S i hC hcheb hzN hz hB)
      (by positivity)

noncomputable def totalTailEnvelope
    (k M B X z L H : ℕ) (C : ℝ) : ℝ :=
  (k : ℝ) * ((X : ℝ) *
      ((6 * B * C / Real.log z) *
        roughReciprocalMass z X ^ (k + 1))) *
    (((L + 1 : ℕ) : ℝ) * (z : ℝ)^L) *
    ((k : ℝ)^L * M * (z : ℝ)^L / (2 * H))

/-- All actual coordinates, split certificates and truncated prime subsets
are retained in this concrete finite tail bound. -/
theorem sum_certificateTailBound_le
    {B K X z y medium second gap L H : ℕ} {S : BPZSection6Input B K}
    {C : ℝ} {N : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B)
    (hX : 0 < X) (hH : 0 < H) :
    (∑ i : Fin S.k, ∑ t ∈ Certificates S X z y medium second gap i,
      ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        if T.card ≤ L then
          certificateTailBound t (∏ p ∈ T, p) H else 0) ≤
      totalTailEnvelope S.k (refinementModulus S) B X z L H C := by
  classical
  let E : ℝ := (S.k : ℝ)^L * refinementModulus S * (z : ℝ)^L / (2 * H)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hper (i : Fin S.k) (t : SplitCertificate S X)
      (ht : t ∈ Certificates S X z y medium second gap i) :
      (∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        if T.card ≤ L then certificateTailBound t (∏ p ∈ T, p) H else 0) ≤
        (((L + 1 : ℕ) : ℝ) * (z : ℝ)^L) * E := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ _T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset.filter
          (fun T => T.card ≤ L), E := by
        apply Finset.sum_le_sum
        intro T hT
        obtain ⟨hTP,hTL⟩ := Finset.mem_filter.mp hT
        have hsub := Finset.mem_powerset.mp hTP
        have hprime : ∀ p ∈ T, p.Prime := fun p hp =>
          (MediumSieveEuler.mem_windowPrimes.mp (hsub hp)).1
        have hgL : (∏ p ∈ T, p).primeFactors.card ≤ L := by
          simpa [Nat.primeFactors_prod hprime] using hTL
        have hgG : (∏ p ∈ T, p) ≤ z ^ L := by
          calc
            _ ≤ ∏ _p ∈ T, z := Finset.prod_le_prod
              (fun p hp => Nat.zero_le _) (fun p hp =>
                (MediumSieveEuler.mem_windowPrimes.mp (hsub hp)).2.2.le)
            _ = z ^ T.card := by simp
            _ ≤ z ^ L := Nat.pow_le_pow_right (by omega) hTL
        simpa [E] using certificateTailBound_le t hX hH
          (SeparatedCertificateEnlargement.admissible ht).upper hgL hgG
      _ = (((MediumSieveEuler.windowPrimes S.k z).powerset.filter
          (fun T => T.card ≤ L)).card : ℝ) * E := by simp
      _ ≤ _ := by
        have hsub : MediumSieveEuler.windowPrimes S.k z ⊆ Finset.range z :=
          fun p hp => Finset.mem_range.mpr
            (MediumSieveEuler.mem_windowPrimes.mp hp).2.2
        have hcard := MediumEndpointError.card_truncated_powerset_le
          (L := L) hsub (by omega : 1 ≤ z)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE
  calc
    _ ≤ ∑ i : Fin S.k, ∑ _t ∈ Certificates S X z y medium second gap i,
        ((((L + 1 : ℕ) : ℝ) * (z : ℝ)^L) * E) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (hper i)
    _ ≤ ∑ _i : Fin S.k,
        ((X : ℝ) * ((6 * B * C / Real.log z) *
          roughReciprocalMass z X ^ (S.k + 1))) *
        ((((L + 1 : ℕ) : ℝ) * (z : ℝ)^L) * E) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (card_certificates_le S i hC hcheb hzN hz hB hX)
        (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      unfold totalTailEnvelope
      dsimp [E]
      ring

/-- The actual signed mass-minus-finite-partial sum has a fully explicit
tail.  No cancellation estimate is supplied as a premise. -/
theorem abs_signed_mass_sub_windowPartial_le
    {B K X z y medium second gap L H : ℕ} {S : BPZSection6Input B K}
    {C : ℝ} {N : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B)
    (hX : 0 < X) (hH : 0 < H) :
    |∑ i : Fin S.k, ∑ t ∈ Certificates S X z y medium second gap i,
      ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        MediumSignedMainTerm.coefficient L T *
          (residueMass X (∏ p ∈ T, p) S.k (integerClass t.1) -
            windowCertificatePartial i t z medium H T)| ≤
      totalTailEnvelope S.k (refinementModulus S) B X z L H C := by
  classical
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hsum := sum_certificateTailBound_le (S := S) (X := X) (z := z)
    (y := y) (medium := medium) (second := second) (gap := gap) (L := L) (H := H)
    hC hcheb hzN hz hB hX hH
  refine le_trans ?_ hsum
  apply Finset.sum_le_sum
  intro i hi
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro t ht
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  by_cases hTL : T.card ≤ L
  · rw [MediumSignedMainTerm.coefficient, if_pos hTL, abs_mul, abs_pow]
    simpa only [abs_neg, abs_one, one_pow, one_mul, if_pos hTL] using
      abs_certificateMass_sub_partial_le hX hH ht hT
  · simp [MediumSignedMainTerm.coefficient,hTL]

end Erdos387Proof.SeparatedFourierTail
