import Erdos387Proof.ConvenientCertificateEnlargement
import Erdos387Proof.ConvenientMainMass
import Erdos387Proof.ConvenientPhaseData
import Erdos387Proof.MediumFourierTail

/-!
# Finite Fourier tail for the convenient range

This is the actual enlarged-certificate analogue of the medium-range finite
Fourier truncation.  Every distinguished coordinate, full split certificate,
prime subset and compatible local root remains in the finite sum.  Roughness
of every actual factor discharges coprimality with the sieve product; the tail
estimate itself is reused from the already verified finite progression bound.
-/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientFourierTail

open Erdos387 Erdos387.CoverBPZ
open ConvenientCertificateCover ConvenientCertificateEnlargement
open ConvenientMainMass ConvenientPhaseData
open IntegerSieveResidues MediumFourierTail MediumSieveSmoothing
open scoped BigOperators

noncomputable abbrev Certificates {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium : ℕ) (i : Fin S.k) :=
  ConvenientCertificateEnlargement.certificates S X z y medium i

/-- Prime-window products carry exactly the support data used by roughness. -/
theorem windowProduct_data {k z : ℕ}
    (hk : 0 < k) {T : Finset ℕ}
    (hT : T ∈ (MediumSieveEuler.windowPrimes k z).powerset) :
    Squarefree (∏ p ∈ T, p) ∧
      ∀ p ∈ (∏ q ∈ T, q).primeFactors, max (2 * k) 3 ≤ p ∧ p < z := by
  have hsub := Finset.mem_powerset.mp hT
  have hprime : ∀ p ∈ T, p.Prime := fun p hp =>
    (MediumSieveEuler.mem_windowPrimes.mp (hsub hp)).1
  constructor
  · exact MediumSignedMainTerm.primeSubsetProduct_squarefree
      (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1) hsub
  · rw [Nat.primeFactors_prod hprime]
    intro p hp
    have hwin := MediumSieveEuler.mem_windowPrimes.mp (hsub hp)
    exact ⟨by apply max_le <;> omega,hwin.2.2⟩

/-- The full certificate class modulus is coprime to every actual sieve
product.  This uses all-factor roughness and does not discard a gcd overlap. -/
theorem certificateClassModulus_coprime
    {B K X z y medium g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ Certificates S X z y medium i) (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors, max (2 * S.k) 3 ≤ p ∧ p < z) :
    (refinementModulus S * t.1.val.value).Coprime g := by
  have hd := sieve_applicability ht hg hsupport
  have hr := Nat.coprime_mul_iff_right.mp hd.2.2.2.2.2.1
  have hs := Nat.coprime_mul_iff_right.mp hd.2.2.2.2.2.2
  rw [← t.1.val.factor_mul_otherValue i,
    ConvenientCertificateEnlargement.factor_eq ht]
  have hMD := Nat.coprime_mul_iff_left.mp hd.2.2.1.symm
  exact hMD.1.mul_left ((hr.2.mul_left hs.2).mul_left hMD.2)

/-- Exact finite Fourier partial sum for one actual split certificate and
prime subset.  Values outside the finite domain are immaterial and set to
zero, making this a total function for later finite sums. -/
noncomputable def windowCertificatePartial {B K X : ℕ}
    {S : BPZSection6Input B K} (i : Fin S.k) (t : SplitCertificate S X)
    (z y medium H : ℕ) (T : Finset ℕ) : ℝ := by
  classical
  exact if ht : t ∈ Certificates S X z y medium i then
    if hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset then
      let g := ∏ p ∈ T, p
      let hg := (windowProduct_data
        (by have := S.hk3; omega : 0 < S.k) hT).1
      letI : NeZero g := ⟨hg.ne_zero⟩
      MediumFourierTail.certificatePartial t.1 g H
        (certificateClassModulus_coprime ht hg (windowProduct_data
          (by have := S.hk3; omega : 0 < S.k) hT).2)
    else 0
  else 0

noncomputable def certificateTailBound {B K X : ℕ}
    {S : BPZSection6Input B K} (t : SplitCertificate S X)
    (g H : ℕ) : ℝ :=
  (S.k : ℝ) ^ g.primeFactors.card *
    ((refinementModulus S * t.1.val.value * g : ℕ) : ℝ) / (2 * X * H)

/-- The finite progression estimate applied to one actual enlarged
certificate.  All compatibility hypotheses are derived from its roughness. -/
theorem abs_certificateMass_sub_partial_le
    {B K X z y medium H : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    {t : SplitCertificate S X} {T : Finset ℕ}
    (hX : 0 < X) (hH : 0 < H)
    (ht : t ∈ Certificates S X z y medium i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset) :
    |residueMass X (∏ p ∈ T, p) S.k (integerClass t.1) -
        windowCertificatePartial i t z y medium H T| ≤
      certificateTailBound t (∏ p ∈ T, p) H := by
  classical
  let g := ∏ p ∈ T, p
  have hk : 0 < S.k := by have := S.hk3; omega
  have hg := (windowProduct_data hk hT).1
  have hsupport := (windowProduct_data hk hT).2
  let : NeZero g := ⟨hg.ne_zero⟩
  let : NeZero (refinementModulus S * t.1.val.value) :=
    ⟨(Nat.mul_pos (refinementModulus_pos S) t.1.val.value_pos).ne'⟩
  have hlarge : ∀ p ∈ g.primeFactors, S.k < p := by
    intro p hp
    have hlo := (le_max_left (2 * S.k) 3).trans (hsupport p hp).1
    have := S.hk3
    omega
  have heq : integerClass t.1 = fun n =>
      Int.ModEq (refinementModulus S * t.1.val.value : ℕ) n
        (simultaneousResidue t.1.property (refinementResidue S)
          t.1.val.crtResidue : ℤ) := by
    funext n
    exact propext (IntegerClassFourier.integerClass_iff_combined t.1 n)
  simp only [windowCertificatePartial, dif_pos ht, dif_pos hT]
  rw [heq]
  exact MediumFourierTail.abs_residueMass_sub_partial_le hX hH hg
    (certificateClassModulus_coprime ht hg hsupport) hlarge

theorem certificateTailBound_le
    {B K X H L G g : ℕ} {S : BPZSection6Input B K}
    (t : SplitCertificate S X) (hX : 0 < X) (hH : 0 < H)
    (hval : t.1.val.value ≤ X)
    (hgL : g.primeFactors.card ≤ L) (hgG : g ≤ G) :
    certificateTailBound t g H ≤
      (S.k : ℝ)^L * refinementModulus S * G / (2 * H) := by
  have hk : (1 : ℝ) ≤ S.k := by
    exact_mod_cast (show 1 ≤ S.k by have := S.hk3; omega)
  have hq : refinementModulus S * t.1.val.value * g ≤
      refinementModulus S * X * G := by gcongr
  have hqR : ((refinementModulus S * t.1.val.value * g : ℕ) : ℝ) ≤
      refinementModulus S * (X : ℝ) * G := by exact_mod_cast hq
  unfold certificateTailBound
  calc
    _ ≤ (S.k : ℝ)^L * (refinementModulus S * (X : ℝ) * G) /
        (2 * X * H) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (pow_le_pow_right₀ hk hgL) hqR
        (by positivity) (by positivity)
    _ = _ := by
      have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
      field_simp

/-- Rigorous certificate count obtained from the reciprocal-mass estimate:
every actual certificate has positive value at most `X`. -/
theorem card_certificates_le
    {B K X z y medium : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) {C : ℝ} {N : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B) (hX : 0 < X)
    (hy : 0 < y) :
    ((Certificates S X z y medium i).card : ℝ) ≤
      (X : ℝ) * ((6 * B * C / Real.log z) *
        roughReciprocalMass z X ^ (S.k + 1)) := by
  classical
  calc
    _ = ∑ t ∈ Certificates S X z y medium i, (1 : ℝ) := by simp
    _ ≤ ∑ t ∈ Certificates S X z y medium i,
        (X : ℝ) * ((1 : ℝ) / t.1.val.value) := by
      apply Finset.sum_le_sum
      intro t ht
      have hval := (Finset.mem_filter.mp ht).2.1
      have hv : (0 : ℝ) < t.1.val.value := by exact_mod_cast t.1.val.value_pos
      calc
        (1 : ℝ) = (t.1.val.value : ℝ) / t.1.val.value := by field_simp
        _ ≤ (X : ℝ) / t.1.val.value :=
          div_le_div_of_nonneg_right (by exact_mod_cast hval) hv.le
        _ = (X : ℝ) * ((1 : ℝ) / t.1.val.value) := by ring
    _ = (X : ℝ) *
        (∑ t ∈ Certificates S X z y medium i,
          (1 : ℝ) / t.1.val.value) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_certificates_reciprocal_le S i hC hcheb hzN hz hB hy)
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
    {B K X z y medium L H : ℕ} {S : BPZSection6Input B K}
    {C : ℝ} {N : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B)
    (hX : 0 < X) (hH : 0 < H) (hy : 0 < y) :
    (∑ i : Fin S.k, ∑ t ∈ Certificates S X z y medium i,
      ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        if T.card ≤ L then
          certificateTailBound t (∏ p ∈ T, p) H else 0) ≤
      totalTailEnvelope S.k (refinementModulus S) B X z L H C := by
  classical
  let E : ℝ := (S.k : ℝ)^L * refinementModulus S * (z : ℝ)^L / (2 * H)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hper (i : Fin S.k) (t : SplitCertificate S X)
      (ht : t ∈ Certificates S X z y medium i) :
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
          (Finset.mem_filter.mp ht).2.1 hgL hgG
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
    _ ≤ ∑ i : Fin S.k, ∑ _t ∈ Certificates S X z y medium i,
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
        (card_certificates_le S i hC hcheb hzN hz hB hX hy)
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
    {B K X z y medium L H : ℕ} {S : BPZSection6Input B K}
    {C : ℝ} {N : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B)
    (hX : 0 < X) (hH : 0 < H) (hy : 0 < y) :
    |∑ i : Fin S.k, ∑ t ∈ Certificates S X z y medium i,
      ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        MediumSignedMainTerm.coefficient L T *
          (residueMass X (∏ p ∈ T, p) S.k (integerClass t.1) -
            windowCertificatePartial i t z y medium H T)| ≤
      totalTailEnvelope S.k (refinementModulus S) B X z L H C := by
  classical
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hsum := sum_certificateTailBound_le
    (S := S) (X := X) (z := z) (y := y) (medium := medium)
    (L := L) (H := H) (C := C) (N := N)
    hC hcheb hzN hz hB hX hH hy
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

end Erdos387Proof.ConvenientFourierTail
