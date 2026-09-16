import Erdos387Proof.SquarefreeTuple
import ErdosProblems.Erdos387.MediumCertificates

/-! Independent medium certificates. The varying coordinate is deliberately
not required to be squarefree or rough in this enlarged nonnegative cover. -/

namespace Erdos387Proof.MediumCertificateCover

open Erdos387 Erdos387.CoverBPZ
open scoped BigOperators

noncomputable def certificates {B K : ℕ} (S : BPZSection6Input B K)
    (X z medium large : ℕ) (i : Fin S.k) :
    Finset (RefinedTupleCertificate S X) := by
  classical
  exact Finset.univ.filter fun C =>
    C.val.value ≤ X ∧ X / 2 < B * C.val.value ∧
      medium < C.val.factor i ∧ C.val.factor i ≤ large ∧
      ∀ j, j ≠ i → Squarefree (C.val.factor j) ∧ IsZRough z (C.val.factor j)

/-- The cover preserves the near-divisor product window and all complementary
rough squarefree coordinates, while dropping restrictions on the varying
coordinate before any signed sieve expansion. -/
theorem exists_certificate {B K X z medium large n : ℕ}
    (S : BPZSection6Input B K) (hz : 2 * S.k ≤ z)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (hnErr : n ∈ RefinedMediumErrors S X z medium large) :
    ∃ (i : Fin S.k) (C : RefinedTupleCertificate S X),
      C ∈ certificates S X z medium large i ∧ n ∈ C.classIoc (X / 2) X := by
  classical
  obtain ⟨hn, hprog, i, E, D, hD, hprod, hmedium, hlarge, hnear, hvaln,
      hDpos, hmediumD, hlower⟩ := mediumError_coordinate_data S hnErr
  have hnData := hnSq
  rw [RefinedSquarefreeCandidates, Finset.mem_filter,
    RefinedSiftedCandidates, Finset.mem_filter, mem_RefinedBaseCandidates] at hnData
  have hnIoc := hnData.1.1.1
  have hvalX : E.value ≤ X := hvaln.trans (Finset.mem_Ioc.mp hnIoc).2
  obtain ⟨hfactorSq, hvalueSq, hotherSq⟩ :=
    coverDivisorTuple_squarefree_data S hnSq hn hprog E
  obtain ⟨hMvalue, hvalueRough⟩ :=
    coverDivisorTuple_rough_data S hnSq hn hprog E hz
  have hdvd (j : Fin S.k) : E.factor j ∣ E.value :=
    Finset.dvd_prod_of_mem E.factor (Finset.mem_univ j)
  have hpos (j : Fin S.k) : 0 < E.factor j :=
    Nat.pos_of_ne_zero (hfactorSq j).ne_zero
  have hfactorX (j : Fin S.k) : E.factor j ≤ X :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hvalueSq.ne_zero) (hdvd j)).trans hvalX
  have hpair (a b : Fin S.k) (hab : a ≠ b) :
      Nat.Coprime (E.factor a) (E.factor b) :=
    Nat.Coprime.of_dvd_right (E.divides b)
      (Nat.Coprime.of_dvd_left (E.divides a)
        (S.coverQuotients_pairwise_coprime hn hprog
          a a.isLt b b.isLt (fun h => hab (Fin.ext h))))
  let C₀ : TupleCertificate S.k X :=
    ⟨fun j => ⟨E.factor j, by have := hfactorX j; omega⟩, hpos, hpair⟩
  let C : RefinedTupleCertificate S X := ⟨C₀, hMvalue⟩
  refine ⟨i, C, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hvalX,
      (Finset.mem_Ioc.mp hnIoc).1.trans hnear, hmedium, hlarge, ?_⟩
    intro j hj
    refine ⟨hfactorSq j, ?_⟩
    intro p hp hpz hpj
    have hpval : p ∈ E.value.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpj.trans (hdvd j), hvalueSq.ne_zero⟩
    exact (not_lt_of_ge (hvalueRough p hpval)) hpz
  · apply (RefinedTupleCertificate.mem_classIoc_iff C).mpr
    refine ⟨hnIoc, (refinement_progression_dvd_iff_modEq S).mp hnData.1.1.2.2, ?_⟩
    apply C₀.ambient_modEq_crtResidue hn.le hvaln
    intro j
    exact (E.divides j).trans
      (coverQuotient_dvd_term (S.toCoverFactorization hn hprog) j.isLt)

noncomputable def siftedClass {B K X : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (z : ℕ) : Finset ℕ := by
  classical
  exact (C.classIoc (X / 2) X).filter (fun n => n ∈ RefinedSiftedCandidates S X z)

theorem card_inter_le_sum_siftedClass {B K X z medium large : ℕ}
    (S : BPZSection6Input B K) (hz : 2 * S.k ≤ z) :
    (RefinedSquarefreeCandidates S X z ∩
      RefinedMediumErrors S X z medium large).card ≤
      ∑ i : Fin S.k, ∑ C ∈ certificates S X z medium large i,
        (siftedClass C z).card := by
  classical
  let T := (Finset.univ : Finset (Fin S.k)).biUnion fun i =>
    (certificates S X z medium large i).biUnion fun C => siftedClass C z
  have hsub : RefinedSquarefreeCandidates S X z ∩
      RefinedMediumErrors S X z medium large ⊆ T := by
    intro n hn
    obtain ⟨hnSq, hnErr⟩ := Finset.mem_inter.mp hn
    obtain ⟨i, C, hC, hnC⟩ := exists_certificate S hz hnSq hnErr
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨C, hC, ?_⟩⟩
    exact Finset.mem_filter.mpr ⟨hnC, (Finset.mem_filter.mp hnSq).1⟩
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.card_biUnion_le

end Erdos387Proof.MediumCertificateCover
