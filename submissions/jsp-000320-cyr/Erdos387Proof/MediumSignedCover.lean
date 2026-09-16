import Erdos387Proof.MediumComplementGrouping
import Erdos387Proof.MediumSignedMainTerm
import Erdos387Proof.IntegerSieveResidues

/-! Exact prime-subset conversion and complementary regrouping of the
nonnegative medium-error cover. No signed sum is enlarged here. -/

namespace Erdos387Proof.MediumSignedCover

open Erdos387 MediumCertificateCover MediumFactorWindow MediumComplementGrouping
open IntegerBrunSmoothing IntegerSieveResidues MediumSieveSmoothing
open scoped BigOperators

theorem subsetMass_eq_primeProduct_residueMass (P : Finset ℕ) (k X : ℕ)
    (R : ℤ → Prop) (hP : ∀ p ∈ P, p.Prime) {T : Finset ℕ} (hT : T ∈ P.powerset) :
    subsetMass P k X R T = residueMass X (∏ p ∈ T, p) k R := by
  have hsub := Finset.mem_powerset.mp hT
  have hprime : ∀ p ∈ T, p.Prime := fun p hp => hP p (hsub hp)
  have hpf := Nat.primeFactors_prod hprime
  have he := subsetMass_eq_residueMass (k := k) (X := X)
    (MediumSignedMainTerm.primeSubsetProduct_squarefree hP hsub)
    (show (∏ p ∈ T, p).primeFactors ⊆ P by rwa [hpf]) R
  simpa only [hpf] using he

theorem weightedMass_eq_signed_residueMass (P : Finset ℕ) (k L X : ℕ)
    (R : ℤ → Prop) (hP : ∀ p ∈ P, p.Prime) :
    weightedMass P k L X R =
      ∑ T ∈ P.powerset, MediumSignedMainTerm.coefficient L T *
        residueMass X (∏ p ∈ T, p) k R := by
  rw [weightedMass_eq_sum_subsets]
  apply Finset.sum_congr rfl
  intro T hT
  rw [subsetMass_eq_primeProduct_residueMass P k X R hP hT]
  rfl

/-- The original squarefree-medium intersection is bounded by the exact
signed residue masses, grouped by all k-1 fixed coordinates and one
coprime factor interval. -/
theorem card_medium_le_signed_grouped_residueMass {B K X z medium large L : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (P : Finset ℕ)
    (hB : 0 < B) (hz : 2 * S.k ≤ z) (hX : 0 < X) (hL : Even L)
    (hP : ∀ p ∈ P, p.Prime ∧ S.k < p ∧ p < z) :
    ((CoverBPZ.RefinedSquarefreeCandidates S X z ∩
      CoverBPZ.RefinedMediumErrors S X z medium large).card : ℝ) ≤
      ∑ i : Fin S.k, ∑ c ∈ (vectors S X z medium large i).attach,
        ∑ d ∈ factors B X ((representative c).val.otherValue i)
            (CoverBPZ.refinementModulus S) medium large,
          ∑ T ∈ P.powerset, MediumSignedMainTerm.coefficient L T *
            residueMass X (∏ p ∈ T, p) S.k
              (integerClass (fromFactor (representative c) i medium large d)) := by
  have h := card_medium_le_sum_weightedMass
    (medium := medium) (large := large) S P hz hX hL hP
  have heq :
      (∑ i : Fin S.k, ∑ C ∈ certificates S X z medium large i,
        weightedMass P S.k L X (integerClass C)) =
      ∑ i : Fin S.k, ∑ c ∈ (vectors S X z medium large i).attach,
        ∑ d ∈ factors B X ((representative c).val.otherValue i)
            (CoverBPZ.refinementModulus S) medium large,
          ∑ T ∈ P.powerset, MediumSignedMainTerm.coefficient L T *
            residueMass X (∏ p ∈ T, p) S.k
              (integerClass (fromFactor (representative c) i medium large d)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [sum_certificates_eq_sum_factors i hB]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    exact weightedMass_eq_signed_residueMass P S.k L X _ (fun p hp => (hP p hp).1)
  exact h.trans_eq heq

end Erdos387Proof.MediumSignedCover
