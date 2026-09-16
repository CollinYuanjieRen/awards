import Erdos387Proof.ConvenientCertificateEnlargement
import Erdos387Proof.ConvenientComplementGrouping
import Erdos387Proof.MediumSignedCover

/-!
# Signed finite cover for the convenient range

The squarefree convenient-error intersection is first enlarged only through
nonnegative class cardinalities.  Each enlarged class is then bounded by its
Brun weighted mass.  Only after this inequality do we use the exact signed
prime-subset expansion.  The final equality groups certificates in two levels:
the complementary vector is the sole outer moment index, and the ordered split
pair remains in its finite inner fibre.
-/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientSignedCover

open Erdos387
open Erdos387.CoverBPZ
open ConvenientCertificateCover ConvenientComplementGrouping
open IntegerBrunSmoothing IntegerSieveResidues MediumSieveSmoothing
open scoped BigOperators

noncomputable abbrev EnlargedCertificates {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium : ℕ) (i : Fin S.k) : Finset (SplitCertificate S X) :=
  ConvenientCertificateEnlargement.certificates S X z y medium i

/-- The exact signed residue-mass expansion attached to one refined tuple. -/
noncomputable def signedResidueMass {B K X : ℕ}
    {S : BPZSection6Input B K} (P : Finset ℕ) (L : ℕ)
    (C : RefinedTupleCertificate S X) : ℝ :=
  ∑ T ∈ P.powerset, MediumSignedMainTerm.coefficient L T *
    residueMass X (∏ p ∈ T, p) S.k (integerClass C)

theorem weightedMass_eq_signedResidueMass {B K X L : ℕ}
    {S : BPZSection6Input B K} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (C : RefinedTupleCertificate S X) :
    weightedMass P S.k L X (integerClass C) = signedResidueMass P L C := by
  exact MediumSignedCover.weightedMass_eq_signed_residueMass
    P S.k L X (integerClass C) hP

/-- The nonnegative enlargement is still bounded pointwise by the Brun
weighted masses.  No signed summand has been enlarged at this stage. -/
theorem card_convenient_le_sum_weightedMass
    {B K X z y medium L : ℕ}
    (S : BPZSection6Input B K) (P : Finset ℕ)
    (hz : 2 * S.k ≤ z) (hX : 0 < X) (hL : Even L)
    (hP : ∀ p ∈ P, p.Prime ∧ S.k < p ∧ p < z) :
    ((RefinedSquarefreeCandidates S X z ∩
      RefinedConvenientErrors S X z y medium).card : ℝ) ≤
      ∑ i : Fin S.k, ∑ t ∈ EnlargedCertificates S X z y medium i,
        weightedMass P S.k L X (integerClass t.1) := by
  have hc :
      ((RefinedSquarefreeCandidates S X z ∩
        RefinedConvenientErrors S X z y medium).card : ℝ) ≤
        ∑ i : Fin S.k, ∑ t ∈ EnlargedCertificates S X z y medium i,
          ((MediumCertificateCover.siftedClass t.1 z).card : ℝ) := by
    exact_mod_cast ConvenientCertificateEnlargement.card_inter_le_sum_classes S hz
  apply hc.trans
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro t ht
  exact card_siftedClass_le_weightedMass S t.1 P hX hL hP

/-- Exact nested regrouping of all enlarged Brun masses.  The selected
coordinate factorization is used only to recover the unique certificate from
its complement and ordered split pair. -/
theorem sum_weightedMass_eq_nested_signedResidueMass
    {B K X z y medium L : ℕ}
    (S : BPZSection6Input B K) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ i : Fin S.k, ∑ t ∈ EnlargedCertificates S X z y medium i,
        weightedMass P S.k L X (integerClass t.1)) =
      ∑ i : Fin S.k,
        ∑ c ∈ (complementVectorsOf i
            (EnlargedCertificates S X z y medium i)).attach,
          ∑ p ∈ (splitPairFibreOf i
              (EnlargedCertificates S X z y medium i) c.val).attach,
            signedResidueMass P L (pairRepresentativeOf c p).1 := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_family_eq_sum_complements_splitPairs i
    (EnlargedCertificates S X z y medium i)
    (fun t ht => ConvenientCertificateEnlargement.factor_eq ht)]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro p hp
  exact weightedMass_eq_signedResidueMass P hP (pairRepresentativeOf c p).1

/-- Actual convenient errors are bounded by a finite signed residue-mass sum.
The nonnegative enlargement precedes the signed expansion, and the final outer
moment index is exactly the complementary vector. -/
theorem card_convenient_le_nested_signedResidueMass
    {B K X z y medium L : ℕ}
    (S : BPZSection6Input B K) (P : Finset ℕ)
    (hz : 2 * S.k ≤ z) (hX : 0 < X) (hL : Even L)
    (hP : ∀ p ∈ P, p.Prime ∧ S.k < p ∧ p < z) :
    ((RefinedSquarefreeCandidates S X z ∩
      RefinedConvenientErrors S X z y medium).card : ℝ) ≤
      ∑ i : Fin S.k,
        ∑ c ∈ (complementVectorsOf i
            (EnlargedCertificates S X z y medium i)).attach,
          ∑ p ∈ (splitPairFibreOf i
              (EnlargedCertificates S X z y medium i) c.val).attach,
            signedResidueMass P L (pairRepresentativeOf c p).1 := by
  exact (card_convenient_le_sum_weightedMass S P hz hX hL hP).trans_eq
    (sum_weightedMass_eq_nested_signedResidueMass S P
      (fun p hp => (hP p hp).1))

end Erdos387Proof.ConvenientSignedCover
