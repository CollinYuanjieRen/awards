import Erdos387Proof.ConvenientMassDecomposition
import Erdos387Proof.ConvenientFourierTailDecay
import Erdos387Proof.MediumPartialFourier

/-! The remaining convenient error is exactly the actual finite nonzero
Fourier sum. Zero modes and the fully summed truncation tail are separated
by identities before any absolute-value estimate. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientPartialFourier
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open ConvenientZeroMode ConvenientFourierTail ConvenientMassDecomposition
open MediumFourierTailDecay MediumSubpowerReduction Filter
open scoped BigOperators Topology

noncomputable def partialRemainder {B K X : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (t : SplitCertificate S X) (z y medium H : ℕ) (T : Finset ℕ) : ℝ :=
  ConvenientFourierTail.windowCertificatePartial i t z y medium H T-
    certificateZero t (∏ p ∈ T,p)

/-- Every original support and no-aliasing condition is checked at the actual
certificate; the retained modes are exactly the nonzero integer window. -/
theorem partialRemainder_eq_nonzeroPartial {B K X z y medium H : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X} {T : Finset ℕ}
    (ht : t∈ConvenientCertificateEnlargement.certificates S X z y medium i)
    (hT : T∈(MediumSieveEuler.windowPrimes S.k z).powerset) (hX : 0<X)
    (hHq : 2*H<refinementModulus S*t.1.val.value*(∏ p ∈ T,p)) :
    let hk : 0<S.k := by have := S.hk3; omega
    let hg := (windowProduct_data hk hT).1
    letI : NeZero (∏ p ∈ T,p) := ⟨hg.ne_zero⟩
    partialRemainder i t z y medium H T=
      MediumPartialFourier.certificateNonzeroPartial t.1 (∏ p ∈ T,p) H
        (certificateClassModulus_coprime ht hg (windowProduct_data hk hT).2) := by
  classical
  have hk : 0<S.k := by have := S.hk3; omega
  have hg := (windowProduct_data hk hT).1
  let : NeZero (∏ p ∈ T,p) := ⟨hg.ne_zero⟩
  have hl : ∀ p ∈ (∏ p ∈ T,p).primeFactors, S.k<p := by
    intro p hp
    have := (windowProduct_data hk hT).2 p hp
    have := le_max_left (2*S.k) 3
    omega
  unfold partialRemainder ConvenientFourierTail.windowCertificatePartial
  rw [dif_pos ht,dif_pos hT,MediumPartialFourier.certificatePartial_eq_zero_add t.1 hX _ hl hHq]
  unfold certificateZero
  ring

noncomputable def totalPartialRemainder {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  ∑ i : Fin S.k,
    ∑ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i,
    ∑ T ∈ (MediumSieveEuler.windowPrimes S.k (SubpowerScale.z N S.k)).powerset,
      MediumSignedMainTerm.coefficient (2*N) T*partialRemainder i t
        (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
        (height N S.k) T

theorem totalRemainder_eq_partial_add_tail {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    totalRemainder S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (2*N) =
      totalPartialRemainder S N+ConvenientFourierTailDecay.signedTail S N := by
  unfold totalRemainder totalPartialRemainder ConvenientFourierTailDecay.signedTail
    remainder partialRemainder
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

theorem eventually_certificate_window {B K : ℕ} (S : BPZSection6Input B K) (hB : 0<B) :
    ∀ᶠ N : ℕ in atTop, ∀ i : Fin S.k,
      ∀ t ∈ ConvenientCertificateEnlargement.certificates S (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k) (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i,
      ∀ g : ℕ, 0<g → 2*height N S.k<refinementModulus S*t.1.val.value*g := by
  classical
  filter_upwards [eventually_four_mul_height_le_X S.k B (by have := S.hk3; omega)] with N hN
  intro i t ht g hg
  exact two_mul_height_lt_modulus hB (refinementModulus_pos S) hg
    (Finset.mem_filter.mp ht).2.2.1 hN

theorem card_convenient_le_zero_partial_tail {B K : ℕ} (S : BPZSection6Input B K)
    (N : ℕ) (hz : 2*S.k≤SubpowerScale.z N S.k) :
    ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)∩
      RefinedConvenientErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)).card : ℝ) ≤
      totalZeroMass S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) (2*N)+
      |totalPartialRemainder S N|+|ConvenientFourierTailDecay.signedTail S N| := by
  have h := card_convenient_le_zero_add_abs_remainder S
    (y := SubpowerScale.y N S.k) (medium := SubpowerScale.medium N S.k) hz
    (SubpowerScale.X_pos N S.k) (even_two_mul N)
  rw [totalRemainder_eq_partial_add_tail] at h
  have habs := abs_add_le (totalPartialRemainder S N) (ConvenientFourierTailDecay.signedTail S N)
  exact h.trans (by linarith)

end Erdos387Proof.ConvenientPartialFourier
