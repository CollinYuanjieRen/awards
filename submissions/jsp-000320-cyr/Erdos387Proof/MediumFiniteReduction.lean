import Erdos387Proof.MediumSignedCover
import Erdos387Proof.MediumMassDecomposition
import Erdos387Proof.MediumComplementBounds
import Erdos387Proof.MediumMainTermAssembly

/-! Finite reduction of the original medium-error cardinality to the actual
signed Brun main term, harmonic endpoint errors, and explicit Fourier
remainders summed over complete factor intervals. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumFiniteReduction

open Erdos387 MediumFactorWindow MediumComplementGrouping MediumComplementBounds
open MediumCertificateCover MediumSieveSmoothing IntegerSieveResidues
open MediumSignedMainTerm MediumMassDecomposition
open scoped BigOperators

noncomputable def signedFibreMass {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (P : Finset ℕ) (L medium large : ℕ) : ℝ :=
  ∑ T ∈ P.powerset, coefficient L T *
    ∑ d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large,
      residueMass X (∏ p ∈ T, p) S.k (integerClass (fromFactor C i medium large d))

noncomputable def harmonicError {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (P : Finset ℕ) (L medium : ℕ) : ℝ :=
  ∑ T ∈ P.powerset, if T.card ≤ L then
    MediumZeroMode.endpointError (∏ p ∈ T, p)
      (CoverBPZ.refinementModulus S * C.val.otherValue i) S.k
      (lower B X (C.val.otherValue i) medium) (3 * (X : ℝ) + 1) else 0

noncomputable def fourierError {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (P : Finset ℕ) (L medium large : ℕ) : ℝ :=
  ∑ T ∈ P.powerset, if T.card ≤ L then
    |∑ d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large,
      remainder (fromFactor C i medium large d) i (∏ p ∈ T, p)| else 0

noncomputable def fibreMainTerm {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (P : Finset ℕ) (L medium large : ℕ) : ℝ :=
  prefactor (CoverBPZ.refinementModulus S * C.val.otherValue i)
    (lower B X (C.val.otherValue i) medium) (upper X (C.val.otherValue i) large)
    (3 * (X : ℝ) + 1) * brunSubsetSum P (MediumSieveEuler.alpha S.k) L

/-- Cancellation is retained inside each full factor-interval Fourier sum.
Only after that summation is its absolute value taken. -/
theorem signedFibreMass_le {B K X z medium large L : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {C : RefinedTupleCertificate S X}
    {i : Fin S.k} (hC : C ∈ certificates S X z medium large i)
    (hB : 0 < B) (hm : 0 < medium) :
    signedFibreMass C i (MediumSieveEuler.windowPrimes S.k z) L medium large ≤
      fibreMainTerm C i (MediumSieveEuler.windowPrimes S.k z) L medium large +
        harmonicError C i (MediumSieveEuler.windowPrimes S.k z) L medium +
          fourierError C i (MediumSieveEuler.windowPrimes S.k z) L medium large := by
  classical
  let P := MediumSieveEuler.windowPrimes S.k z
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1
  have hQ : 0 < CoverBPZ.refinementModulus S * C.val.otherValue i :=
    Nat.mul_pos (CoverBPZ.refinementModulus_pos S) (C.val.otherValue_pos i)
  have hcp : ∀ p ∈ P, Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) p := by
    intro p hp
    have ht : {p} ∈ P.powerset := Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hp)
    simpa using (window_product_coprime_complement hC ht).symm
  have hself : C ∈ fibre C i z medium large := Finset.mem_filter.mpr ⟨hC, by simp⟩
  have hfac := factor_mem_of_mem_fibre C C i hB hself
  have hAU := Finset.mem_Ioc.mp (Finset.mem_filter.mp hfac).1
  have hzmain := abs_sum_zeroMode_sub_brun_le P S.k L
    (CoverBPZ.refinementModulus S * C.val.otherValue i)
    (lower B X (C.val.otherValue i) medium) (upper X (C.val.otherValue i) large)
    (3 * (X : ℝ) + 1) (by positivity) hQ
    (MediumFactorGeometry.lower_pos hm) (hAU.1.le.trans hAU.2) hP hcp
  have heq : signedFibreMass C i P L medium large =
      (∑ T ∈ P.powerset, coefficient L T *
        MediumZeroMode.zeroMode (∏ p ∈ T, p) (CoverBPZ.refinementModulus S * C.val.otherValue i)
          S.k (lower B X (C.val.otherValue i) medium) (upper X (C.val.otherValue i) large)
          (3 * (X : ℝ) + 1)) +
      ∑ T ∈ P.powerset, coefficient L T *
        ∑ d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large,
          remainder (fromFactor C i medium large d) i (∏ p ∈ T, p) := by
    unfold signedFibreMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    have hg : 0 < ∏ p ∈ T, p := Finset.prod_pos
      (fun p hp => (hP p (Finset.mem_powerset.mp hT hp)).pos)
    rw [sum_residueMass_eq_zeroMode_add_remainder C i hg
      (window_product_coprime_complement hC hT), mul_add]
  have hrem : (∑ T ∈ P.powerset, coefficient L T *
        ∑ d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large,
          remainder (fromFactor C i medium large d) i (∏ p ∈ T, p)) ≤
      fourierError C i P L medium large := by
    apply Finset.sum_le_sum
    intro T hT
    by_cases hTL : T.card ≤ L
    · calc
        _ ≤ |coefficient L T * ∑ d ∈ factors B X (C.val.otherValue i)
              (CoverBPZ.refinementModulus S) medium large,
                remainder (fromFactor C i medium large d) i (∏ p ∈ T, p)| := le_abs_self _
        _ = _ := by simp [coefficient, hTL, abs_mul, abs_pow]
    · simp [coefficient, hTL]
  change signedFibreMass C i P L medium large ≤ _
  rw [heq]
  have hzero := (abs_le.mp hzmain).2
  change _ - fibreMainTerm C i P L medium large ≤ harmonicError C i P L medium at hzero
  linarith

/-- This still displays the Fourier error explicitly; no claim of a small
medium-error count is made until that remaining term is bounded. -/
theorem card_medium_le_sum_reduced {B K X z medium large L : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hB : 0 < B) (hz : 2 * S.k ≤ z) (hX : 0 < X) (hm : 0 < medium) (hL : Even L) :
    ((CoverBPZ.RefinedSquarefreeCandidates S X z ∩
      CoverBPZ.RefinedMediumErrors S X z medium large).card : ℝ) ≤
      ∑ i : Fin S.k, ∑ c ∈ (vectors S X z medium large i).attach,
        (fibreMainTerm (representative c) i (MediumSieveEuler.windowPrimes S.k z) L medium large +
          harmonicError (representative c) i (MediumSieveEuler.windowPrimes S.k z) L medium +
            fourierError (representative c) i (MediumSieveEuler.windowPrimes S.k z) L medium large) := by
  have hP : ∀ p ∈ MediumSieveEuler.windowPrimes S.k z, p.Prime ∧ S.k < p ∧ p < z := by
    intro p hp
    obtain ⟨hpp, hlow, hhigh⟩ := MediumSieveEuler.mem_windowPrimes.mp hp
    have hk := S.hk3
    exact ⟨hpp, by omega, hhigh⟩
  apply (MediumSignedCover.card_medium_le_signed_grouped_residueMass
    (medium := medium) (large := large) S _ hB hz hX hL hP).trans
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro c hc
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  exact signedFibreMass_le (representative_mem c) hB hm

end Erdos387Proof.MediumFiniteReduction
