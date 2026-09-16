import Erdos387Proof.SeparatedZeroMode
import Erdos387Proof.ConvenientMassDecomposition

/-! Actual separated-error counting: prime-to-rough enlargement precedes
the signed Brun expansion; zero modes are recombined before absolute values. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedSignedCover
open Erdos387 Erdos387.CoverBPZ SeparatedCertificateEnlargement
open IntegerBrunSmoothing MediumSieveSmoothing ConvenientSignedCover
open ConvenientMassDecomposition (remainder)
open SeparatedZeroMode
open scoped BigOperators

theorem card_separated_le_sum_weightedMass {B K X z y medium second gap L : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k≤z) (hsecond : 1 ≤ second)
    (hX : 0<X) (hL : Even L) :
    ((RefinedSquarefreeCandidates S X z∩
      RefinedSeparatedAlmostPrimeErrors S X z y medium second gap).card : ℝ)≤
      ∑ i : Fin S.k, ∑ t∈certificates S X z y medium second gap i,
        weightedMass (MediumSieveEuler.windowPrimes S.k z) S.k L X (integerClass t.1) := by
  have hc : ((RefinedSquarefreeCandidates S X z∩
      RefinedSeparatedAlmostPrimeErrors S X z y medium second gap).card : ℝ)≤
      ∑ i : Fin S.k, ∑ t∈certificates S X z y medium second gap i,
        ((MediumCertificateCover.siftedClass t.1 z).card : ℝ) := by
    exact_mod_cast card_inter_le_sum_classes S hz hsecond
  apply hc.trans
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro t ht
  apply card_siftedClass_le_weightedMass S t.1 _ hX hL
  intro p hp
  obtain ⟨hp,hl,hu⟩ := MediumSieveEuler.mem_windowPrimes.mp hp
  have := S.hk3
  exact ⟨hp,by omega,hu⟩

noncomputable def totalRemainder {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium second gap L : ℕ) : ℝ :=
  ∑ i : Fin S.k, ∑ t∈certificates S X z y medium second gap i,
    ∑ T∈(MediumSieveEuler.windowPrimes S.k z).powerset,
      MediumSignedMainTerm.coefficient L T*remainder t (∏ p∈T,p)

theorem sum_signedResidueMass_eq_zero_add_remainder {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium second gap L : ℕ) :
    (∑ i : Fin S.k, ∑ t∈certificates S X z y medium second gap i,
      signedResidueMass (MediumSieveEuler.windowPrimes S.k z) L t.1)=
      totalZeroMass S X z y medium second gap L+totalRemainder S X z y medium second gap L := by
  unfold signedResidueMass totalZeroMass totalRemainder remainder
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

theorem card_separated_le_zero_add_abs_remainder {B K X z y medium second gap L : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k≤z) (hsecond : 1 ≤ second)
    (hX : 0<X) (hL : Even L) :
    ((RefinedSquarefreeCandidates S X z∩
      RefinedSeparatedAlmostPrimeErrors S X z y medium second gap).card : ℝ)≤
      totalZeroMass S X z y medium second gap L+|totalRemainder S X z y medium second gap L| := by
  have hc := card_separated_le_sum_weightedMass S (y := y) (medium := medium) (gap := gap)
    hz hsecond hX hL
  simp_rw [weightedMass_eq_signedResidueMass _
    (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)] at hc
  rw [sum_signedResidueMass_eq_zero_add_remainder] at hc
  exact hc.trans (add_le_add le_rfl (le_abs_self _))

end Erdos387Proof.SeparatedSignedCover
