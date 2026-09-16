import Erdos387Proof.ConvenientSignedCover
import Erdos387Proof.ConvenientZeroMode
import Erdos387Proof.ConvenientPhaseData

/-! Exact zero/nonzero decomposition of the actual enlarged convenient
certificate sum. The final counting inequality keeps all signed sums intact. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientMassDecomposition
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open ConvenientZeroMode ConvenientSignedCover ConvenientPhaseData
open IntegerSieveResidues MediumSieveSmoothing MediumCertificateZeroMode
open scoped BigOperators

theorem classModulus_coprime {B K X z y medium g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t∈ConvenientCertificateEnlargement.certificates S X z y medium i)
    (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors, max (2*S.k) 3≤p ∧ p<z) :
    (refinementModulus S*t.1.val.value).Coprime g := by
  have hd := sieve_applicability ht hg hsupport
  have hr := Nat.coprime_mul_iff_right.mp hd.2.2.2.2.2.1
  have hs := Nat.coprime_mul_iff_right.mp hd.2.2.2.2.2.2
  rw [← t.1.val.factor_mul_otherValue i,ConvenientCertificateEnlargement.factor_eq ht]
  have hMD := Nat.coprime_mul_iff_left.mp hd.2.2.1.symm
  exact hMD.1.mul_left ((hr.2.mul_left hs.2).mul_left hMD.2)

noncomputable def remainder {B K X : ℕ} {S : BPZSection6Input B K}
    (t : SplitCertificate S X) (g : ℕ) : ℝ :=
  residueMass X g S.k (integerClass t.1)-certificateZero t g

/-- On the actual domain, this is precisely the nonzero Fourier remainder.
All coprimality follows from the original roughness and the prime window. -/
theorem remainder_eq_classRemainder {B K X z y medium g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t∈ConvenientCertificateEnlargement.certificates S X z y medium i)
    (hX : 0<X) (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors, max (2*S.k) 3≤p ∧ p<z) :
    letI : NeZero g := ⟨hg.ne_zero⟩
    remainder t g=classRemainder t.1 g (classModulus_coprime ht hg hsupport) := by
  let : NeZero g := ⟨hg.ne_zero⟩
  have hlarge : ∀ p ∈ g.primeFactors, S.k<p := by
    intro p hp
    have := (le_max_left (2*S.k) 3).trans (hsupport p hp).1
    have := S.hk3
    omega
  unfold remainder
  rw [residueMass_certificate_eq_main_add t.1 hX hg
    (classModulus_coprime ht hg hsupport) hlarge]
  unfold certificateZero
  ring

noncomputable def totalRemainder {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium L : ℕ) : ℝ :=
  ∑ i : Fin S.k, ∑ t ∈ ConvenientCertificateEnlargement.certificates S X z y medium i,
    ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
      MediumSignedMainTerm.coefficient L T*remainder t (∏ p ∈ T,p)

theorem sum_signedResidueMass_eq_zero_add_remainder {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium L : ℕ) :
    (∑ i : Fin S.k, ∑ t ∈ ConvenientCertificateEnlargement.certificates S X z y medium i,
      signedResidueMass (MediumSieveEuler.windowPrimes S.k z) L t.1) =
      totalZeroMass S X z y medium L+totalRemainder S X z y medium L := by
  unfold signedResidueMass totalZeroMass totalRemainder remainder
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

/-- The actual convenient error cardinality is controlled by the signed zero
mass and a single absolute value of the complete nonzero mass. -/
theorem card_convenient_le_zero_add_abs_remainder {B K X z y medium L : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k≤z) (hX : 0<X) (hL : Even L) :
    ((RefinedSquarefreeCandidates S X z∩RefinedConvenientErrors S X z y medium).card : ℝ) ≤
      totalZeroMass S X z y medium L+|totalRemainder S X z y medium L| := by
  have hP : ∀ p ∈ MediumSieveEuler.windowPrimes S.k z, p.Prime ∧ S.k<p ∧ p<z := by
    intro p hp
    obtain ⟨hp,hl,hu⟩ := MediumSieveEuler.mem_windowPrimes.mp hp
    have := S.hk3
    exact ⟨hp,by omega,hu⟩
  have hc := card_convenient_le_sum_weightedMass S (y := y) (medium := medium)
    (MediumSieveEuler.windowPrimes S.k z) hz hX hL hP
  simp_rw [weightedMass_eq_signedResidueMass _ (fun p hp => (hP p hp).1)] at hc
  rw [sum_signedResidueMass_eq_zero_add_remainder] at hc
  exact hc.trans (add_le_add le_rfl (le_abs_self _))

end Erdos387Proof.ConvenientMassDecomposition
