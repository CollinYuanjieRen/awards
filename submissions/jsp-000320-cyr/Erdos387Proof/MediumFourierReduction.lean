import Erdos387Proof.MediumFiniteReduction
import Erdos387Proof.MediumFourierTail

/-! Truncate after the exact zero-mode subtraction while preserving each
full-factor-interval sum inside its absolute value. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumFourierReduction

open Erdos387 MediumCertificateCover MediumComplementGrouping MediumFactorWindow
open MediumFiniteReduction MediumMassDecomposition MediumFourierTail
open scoped BigOperators

noncomputable def partialRemainder {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (z medium large H : ℕ) (T : Finset ℕ) : ℝ :=
  windowCertificatePartial i C z medium large H T - zeroCoefficient C i (∏ p ∈ T, p)

noncomputable def fibrePartialError {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (z L medium large H : ℕ) : ℝ :=
  ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset, if T.card ≤ L then
    |∑ d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large,
      partialRemainder (fromFactor C i medium large d) i z medium large H T| else 0

private theorem abs_sum_le_abs_sum_add {α : Type} (s : Finset α) (f g : α → ℝ) :
    |∑ a ∈ s, f a| ≤ |∑ a ∈ s, g a| + ∑ a ∈ s, |f a - g a| := by
  have he : (∑ a ∈ s, f a) = (∑ a ∈ s, g a) + ∑ a ∈ s, (f a - g a) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))

/-- Only the tail is bounded term by term. The retained Fourier sum still
runs across the entire varying-factor interval before taking absolute value. -/
theorem fourierError_le_partial_add_tail {B K X z L medium large H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {C : RefinedTupleCertificate S X} {i : Fin S.k}
    (hC : C ∈ certificates S X z medium large i)
    (hB : 0 < B) (hX : 0 < X) (hH : 0 < H) :
    fourierError C i (MediumSieveEuler.windowPrimes S.k z) L medium large ≤
      fibrePartialError C i z L medium large H +
        ∑ d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large,
          ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
            if T.card ≤ L then certificateTailBound (fromFactor C i medium large d) i
              (∏ p ∈ T, p) H else 0 := by
  classical
  unfold fourierError fibrePartialError
  rw [Finset.sum_comm (s := factors B X (C.val.otherValue i)
    (CoverBPZ.refinementModulus S) medium large), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T hT
  by_cases hTL : T.card ≤ L
  · simp only [if_pos hTL]
    apply (abs_sum_le_abs_sum_add _ _ _).trans
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro d hd
    have hCd := (Finset.mem_filter.mp (fromFactor_mem_fibre C i hB
      (Finset.mem_filter.mp hC).2.2.2.2.2 hd)).1
    have h := abs_windowCertificateMass_sub_partial_le hX hH hCd hT
    simpa only [remainder, partialRemainder, sub_sub_sub_cancel_right] using h
  · simp [hTL]

set_option maxHeartbeats 800000 in
/-- All gcd classes, compatible roots, subsets and complementary vectors
are retained in the finite partial error and the proved tail envelope. -/
theorem sum_fourierError_le_partial_add_tail {B K X z L medium large H : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hB : 0 < B) (hX : 0 < X) (hH : 0 < H) (hz : 1 ≤ z) :
    (∑ i : Fin S.k, ∑ c ∈ (vectors S X z medium large i).attach,
      fourierError (representative c) i (MediumSieveEuler.windowPrimes S.k z) L medium large) ≤
      (∑ i : Fin S.k, ∑ c ∈ (vectors S X z medium large i).attach,
        fibrePartialError (representative c) i z L medium large H) +
      totalTailEnvelope S.k (CoverBPZ.refinementModulus S) X z L H := by
  classical
  have hpoint := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := (vectors S X z medium large i).attach) (fun c _ =>
      fourierError_le_partial_add_tail (L := L) (representative_mem c) hB hX hH))
  apply hpoint.trans
  simp only [Finset.sum_add_distrib]
  apply add_le_add le_rfl
  have heq :
      (∑ i : Fin S.k, ∑ c ∈ (vectors S X z medium large i).attach,
        ∑ d ∈ factors B X ((representative c).val.otherValue i) (CoverBPZ.refinementModulus S)
          medium large,
          ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
            if T.card ≤ L then certificateTailBound
              (fromFactor (representative c) i medium large d) i (∏ p ∈ T, p) H else 0) =
      ∑ i : Fin S.k, ∑ C ∈ certificates S X z medium large i,
        ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
          if T.card ≤ L then certificateTailBound C i (∏ p ∈ T, p) H else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (sum_certificates_eq_sum_factors (S := S) (X := X) (z := z)
      (medium := medium) (large := large) i hB
      (fun C => ∑ T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset,
        if T.card ≤ L then certificateTailBound C i (∏ p ∈ T, p) H else 0)).symm
  rw [heq]
  exact sum_certificateTailBound_le _ hB hX hH hz
    (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
    (fun p hp => Finset.mem_range.mpr (MediumSieveEuler.mem_windowPrimes.mp hp).2.2)

end Erdos387Proof.MediumFourierReduction
