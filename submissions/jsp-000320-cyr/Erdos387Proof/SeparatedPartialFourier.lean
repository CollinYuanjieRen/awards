import Erdos387Proof.SeparatedSignedCover
import Erdos387Proof.SeparatedFourierTailDecay
import Erdos387Proof.ConvenientPartialFourier

/-! Exact actual separated-error reduction to its retained finite nonzero
Fourier sum. The signed remainder, zero mass and truncation tail all use
the same enlarged certificate domain. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedPartialFourier
open Erdos387 Erdos387.CoverBPZ SeparatedSignedCover SeparatedZeroMode
open MediumFourierTailDecay MediumSubpowerReduction Filter
open scoped BigOperators Topology

noncomputable def totalPartialRemainder {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  ∑ i : Fin S.k,
    ∑ t∈SeparatedCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
      (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i,
    ∑ T∈(MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
      MediumSignedMainTerm.coefficient (2*N) T*
        ConvenientPartialFourier.partialRemainder i t (SubpowerScale.z N S.k) 0
          (SubpowerScale.medium N S.k) (height N S.k) T

theorem totalRemainder_eq_partial_add_tail {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    totalRemainder S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
      (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) (2*N)=
      totalPartialRemainder S N+SeparatedFourierTailDecay.signedTail S N := by
  unfold totalRemainder totalPartialRemainder SeparatedFourierTailDecay.signedTail
    ConvenientMassDecomposition.remainder ConvenientPartialFourier.partialRemainder
    SeparatedFourierTail.windowCertificatePartial
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

theorem eventually_certificate_window {B K : ℕ} (S : BPZSection6Input B K) (hB : 0<B) :
    ∀ᶠ N : ℕ in atTop, ∀ i : Fin S.k,
      ∀ t∈SeparatedCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
        (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) i,
      ∀ g : ℕ, 0<g → 2*height N S.k<refinementModulus S*t.1.val.value*g := by
  filter_upwards [eventually_four_mul_height_le_X S.k B (by have := S.hk3; omega)] with N hN
  intro i t ht g hg
  exact two_mul_height_lt_modulus hB (refinementModulus_pos S) hg
    (SeparatedCertificateEnlargement.admissible ht).near hN

theorem card_separated_le_zero_partial_tail {B K : ℕ} (S : BPZSection6Input B K)
    (N : ℕ) (hz : 2*S.k≤SubpowerScale.z N S.k) :
    ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)∩
      RefinedSeparatedAlmostPrimeErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
        (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k)).card : ℝ)≤
      totalZeroMass S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
        (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k) (2*N)+
      |totalPartialRemainder S N|+|SeparatedFourierTailDecay.signedTail S N| := by
  have hsecond : 1≤SubpowerScale.secondMin N S.k := by
    unfold SubpowerScale.secondMin BPZScale.secondMin SubpowerScale.base
    exact one_le_pow₀ (one_le_pow₀ (by norm_num : 1≤(2 : ℕ)))
  have h := card_separated_le_zero_add_abs_remainder S
    (y := SubpowerScale.y N S.k) (medium := SubpowerScale.medium N S.k)
    (gap := SubpowerScale.gap N S.k) hz hsecond (SubpowerScale.X_pos N S.k) (even_two_mul N)
  rw [totalRemainder_eq_partial_add_tail] at h
  have habs := abs_add_le (totalPartialRemainder S N) (SeparatedFourierTailDecay.signedTail S N)
  exact h.trans (by linarith)

end Erdos387Proof.SeparatedPartialFourier
