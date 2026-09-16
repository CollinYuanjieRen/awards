import Erdos387Proof.MediumCertificateCover
import Erdos387Proof.IntegerBrunSmoothing

/-! Nonnegative smoothing and exact signed sieve expansion for the actual
medium-error certificate cover. -/

namespace Erdos387Proof.MediumSieveSmoothing

open Erdos387 Erdos387.CoverBPZ
open Erdos387Proof.MediumCertificateCover Erdos387Proof.IntegerBrunSmoothing
open scoped BigOperators

def integerClass {B K X : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (n : ℤ) : Prop :=
  Int.ModEq (refinementModulus S : ℤ) n (refinementResidue S : ℤ) ∧
    Int.ModEq (C.val.value : ℤ) n (C.val.crtResidue : ℤ)

theorem card_siftedClass_le_weightedMass {B K X z L : ℕ}
    (S : BPZSection6Input B K) (C : RefinedTupleCertificate S X) (P : Finset ℕ)
    (hX : 0 < X) (hL : Even L)
    (hP : ∀ p ∈ P, p.Prime ∧ S.k < p ∧ p < z) :
    ((siftedClass C z).card : ℝ) ≤ weightedMass P S.k L X (integerClass C) := by
  classical
  apply card_le_weightedMass P S.k L X (siftedClass C z) (integerClass C) hX hL
  · intro n hn
    have hnC := (Finset.mem_filter.mp hn).1
    exact (Finset.mem_Ioc.mp ((C.mem_classIoc_iff).mp hnC).1).2
  · intro n hn
    have hnC := (C.mem_classIoc_iff).mp (Finset.mem_filter.mp hn).1
    exact ⟨Int.natCast_modEq_iff.mpr hnC.2.1,
      Int.natCast_modEq_iff.mpr hnC.2.2⟩
  · intro n hn
    have hnS := (Finset.mem_filter.mp hn).2
    rw [RefinedSiftedCandidates, Finset.mem_filter, mem_RefinedBaseCandidates] at hnS
    exact no_bad_of_rough hP hnS.1.2.1.le hnS.2

/-- Actual medium errors are bounded by a sum of everywhere nonnegative
integer sieve masses on independent certificates. -/
theorem card_medium_le_sum_weightedMass {B K X z medium large L : ℕ}
    (S : BPZSection6Input B K) (P : Finset ℕ) (hz : 2 * S.k ≤ z)
    (hX : 0 < X) (hL : Even L)
    (hP : ∀ p ∈ P, p.Prime ∧ S.k < p ∧ p < z) :
    ((RefinedSquarefreeCandidates S X z ∩
      RefinedMediumErrors S X z medium large).card : ℝ) ≤
      ∑ i : Fin S.k, ∑ C ∈ certificates S X z medium large i,
        weightedMass P S.k L X (integerClass C) := by
  have hc : ((RefinedSquarefreeCandidates S X z ∩
      RefinedMediumErrors S X z medium large).card : ℝ) ≤
      ∑ i : Fin S.k, ∑ C ∈ certificates S X z medium large i,
        ((siftedClass C z).card : ℝ) := by
    exact_mod_cast card_inter_le_sum_siftedClass
      (medium := medium) (large := large) S hz
  apply hc.trans
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro C hC
  exact card_siftedClass_le_weightedMass S C P hX hL hP

/-- The signed expansion is used only after the nonnegative certificate
enlargement. No sign is discarded from the sieve coefficients. -/
theorem card_medium_le_signed_subset_masses {B K X z medium large L : ℕ}
    (S : BPZSection6Input B K) (P : Finset ℕ) (hz : 2 * S.k ≤ z)
    (hX : 0 < X) (hL : Even L)
    (hP : ∀ p ∈ P, p.Prime ∧ S.k < p ∧ p < z) :
    ((RefinedSquarefreeCandidates S X z ∩
      RefinedMediumErrors S X z medium large).card : ℝ) ≤
      ∑ i : Fin S.k, ∑ C ∈ certificates S X z medium large i,
        ∑ T ∈ P.powerset, (if T.card ≤ L then (-1 : ℝ)^T.card else 0) *
          subsetMass P S.k X (integerClass C) T := by
  simpa only [weightedMass_eq_sum_subsets] using
    card_medium_le_sum_weightedMass (medium := medium) (large := large) S P hz hX hL hP

end Erdos387Proof.MediumSieveSmoothing
