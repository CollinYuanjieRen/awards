import Erdos387Proof.ConvenientCertificateEnlargement
import Erdos387Proof.ConvenientComplementGrouping
import Erdos387Proof.TupleReplacement

/-!
# Exact split-pair fibres for the convenient range

For a fixed full complementary vector, the enlarged certificate fibre is
exactly an independent finite domain in the two ordered split variables.
The domain retains both individual roughness and coprimality conditions and
all three product masks.  This is an equality of finite domains, so it may be
used under signed weights without replacing a signed sum by an inequality.
-/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientSplitFibre

open Erdos387 Erdos387.CoverBPZ
open ConvenientCertificateCover ConvenientComplementGrouping
open MediumComplementGrouping
open scoped BigOperators

noncomputable abbrev EnlargedCertificates {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium : ℕ) (i : Fin S.k) :=
  ConvenientCertificateEnlargement.certificates S X z y medium i

/-- A fixed certificate witnessing a complementary vector.  Its split pair
is irrelevant; only its off-index tuple coordinates are used below. -/
noncomputable def complementRepresentative {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i
      (EnlargedCertificates S X z y medium i)}) : SplitCertificate S X :=
  Classical.choose (Finset.mem_image.mp c.property)

theorem complementRepresentative_mem {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i
      (EnlargedCertificates S X z y medium i)}) :
    complementRepresentative c ∈ EnlargedCertificates S X z y medium i :=
  (Classical.choose_spec (Finset.mem_image.mp c.property)).1

theorem vector_complementRepresentative {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i
      (EnlargedCertificates S X z y medium i)}) :
    vector i (complementRepresentative c).1 = c.val :=
  (Classical.choose_spec (Finset.mem_image.mp c.property)).2

/-- The exact independent split-pair domain over a fixed complement. -/
noncomputable def splitPairDomain {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i
      (EnlargedCertificates S X z y medium i)}) : Finset (ℕ × ℕ) := by
  classical
  let D := (complementRepresentative c).1.val.otherValue i
  let M := refinementModulus S
  exact ((Finset.Ioc y X).product (Finset.Ioc y X)).filter fun p =>
    IsZRough z p.1 ∧ IsZRough z p.2 ∧
      p.1.Coprime (M * D) ∧ p.2.Coprime (M * D) ∧
      p.1 * p.2 ≤ medium ∧
      X / 2 < B * (D * p.1 * p.2) ∧ D * p.1 * p.2 ≤ X

theorem mem_splitPairDomain_iff {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i
      (EnlargedCertificates S X z y medium i)}) {p : ℕ × ℕ} :
    p ∈ splitPairDomain c ↔
      p.1 ∈ Finset.Ioc y X ∧ p.2 ∈ Finset.Ioc y X ∧
      IsZRough z p.1 ∧ IsZRough z p.2 ∧
      p.1.Coprime (refinementModulus S *
        (complementRepresentative c).1.val.otherValue i) ∧
      p.2.Coprime (refinementModulus S *
        (complementRepresentative c).1.val.otherValue i) ∧
      p.1 * p.2 ≤ medium ∧
      X / 2 < B * ((complementRepresentative c).1.val.otherValue i *
        p.1 * p.2) ∧
      (complementRepresentative c).1.val.otherValue i * p.1 * p.2 ≤ X := by
  classical
  simp only [splitPairDomain, Finset.mem_filter]
  constructor
  · rintro ⟨hp,hroughr,hroughs,hcopr,hcops,hmedium,hnear,hupper⟩
    exact ⟨(Finset.mem_product.mp hp).1,(Finset.mem_product.mp hp).2,
      hroughr,hroughs,hcopr,hcops,hmedium,hnear,hupper⟩
  · rintro ⟨hr,hs,hroughr,hroughs,hcopr,hcops,hmedium,hnear,hupper⟩
    exact ⟨Finset.mem_product.mpr ⟨hr,hs⟩,
      hroughr,hroughs,hcopr,hcops,hmedium,hnear,hupper⟩

/-- Membership in the actual enlarged split-pair fibre is exactly membership
in the independent arithmetic domain. -/
theorem mem_splitPairFibreOf_iff {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i
      (EnlargedCertificates S X z y medium i)}) {p : ℕ × ℕ} :
    p ∈ splitPairFibreOf i (EnlargedCertificates S X z y medium i) c.val ↔
      p ∈ splitPairDomain c := by
  classical
  rw [mem_splitPairDomain_iff]
  constructor
  · intro hp
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨htF,hvector⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht0,hX,hnear,hfactor,hall⟩ := Finset.mem_filter.mp htF
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp (Finset.mem_product.mp ht0).2
    have hD : t.1.val.otherValue i =
        (complementRepresentative c).1.val.otherValue i := by
      apply otherValue_eq_of_factors_eq_off_index t.1.val
        (complementRepresentative c).1.val i
      exact (vector_eq_iff i t.1 (complementRepresentative c).1).mp
        (hvector.trans (vector_complementRepresentative c).symm)
    obtain ⟨_,_,hrrough,hsrough,hrcop,hscop⟩ :=
      ConvenientCertificateEnlargement.retained_data htF
    have hvalue :
        (complementRepresentative c).1.val.otherValue i * t.2.1 * t.2.2 =
          t.1.val.value := by
      rw [← t.1.val.factor_mul_otherValue i, hfactor, hD]
      ring
    refine ⟨hr,hs,hrrough,hsrough,?_,?_,?_,?_,?_⟩
    · simpa only [hD] using hrcop
    · simpa only [hD] using hscop
    · simpa only [hfactor] using (hall i).1
    · simpa only [hvalue] using hnear
    · simpa only [hvalue] using hX
  · rintro ⟨hr,hs,hrrough,hsrough,hrcop,hscop,hrsmed,hnear,hupper⟩
    let C := (complementRepresentative c).1
    let D := C.val.otherValue i
    have hr0 : 0 < p.1 := (Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hr).1
    have hs0 : 0 < p.2 := (Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hs).1
    have hd0 : 0 < p.1 * p.2 := Nat.mul_pos hr0 hs0
    have hD0 : 0 < D := C.val.otherValue_pos i
    have hdX : p.1 * p.2 ≤ X := by
      calc
        p.1 * p.2 ≤ D * (p.1 * p.2) :=
          Nat.le_mul_of_pos_left (p.1 * p.2) hD0
        _ = D * p.1 * p.2 := by ring
        _ ≤ X := hupper
    have hcop : (p.1 * p.2).Coprime (refinementModulus S * D) :=
      Nat.Coprime.mul_left hrcop hscop
    let C' : RefinedTupleCertificate S X :=
      TupleReplacement.replaceRefined C i (p.1 * p.2) hd0 hdX hcop
    have hbase := complementRepresentative_mem c
    obtain ⟨_,_,_,_,hbaseAll⟩ := Finset.mem_filter.mp hbase
    have hroughProd : IsZRough z (p.1 * p.2) := by
      intro q hq hqz hqd
      rcases hq.dvd_mul.mp hqd with hqr | hqs
      · exact hrrough q hq hqz hqr
      · exact hsrough q hq hqz hqs
    have hC'mem : (C',p) ∈ EnlargedCertificates S X z y medium i := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ _,Finset.mem_product.mpr ⟨hr,hs⟩⟩,?_,?_,?_,?_⟩
      · rw [TupleReplacement.value_replaceRefined]
        simpa only [C,D, mul_assoc, mul_comm, mul_left_comm] using hupper
      · rw [TupleReplacement.value_replaceRefined]
        simpa only [C,D, mul_assoc, mul_comm, mul_left_comm] using hnear
      · exact TupleReplacement.factor_replaceRefined C i (p.1*p.2)
          hd0 hdX hcop i |>.trans (if_pos rfl)
      · intro j
        by_cases hji : j = i
        · subst j
          rw [TupleReplacement.factor_replaceRefined, if_pos rfl]
          exact ⟨hrsmed,hroughProd,fun h => (h rfl).elim⟩
        · rw [TupleReplacement.factor_replaceRefined, if_neg hji]
          exact hbaseAll j
    apply Finset.mem_image.mpr
    refine ⟨(C',p),Finset.mem_filter.mpr ⟨hC'mem,?_⟩,rfl⟩
    have hvec : vector i C' = vector i C := by
      apply (vector_eq_iff i C' C).mpr
      intro j hji
      exact (TupleReplacement.factor_replaceRefined C i (p.1*p.2)
        hd0 hdX hcop j).trans (if_neg hji)
    exact hvec.trans (vector_complementRepresentative c)

theorem splitPairFibreOf_eq_splitPairDomain {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i
      (EnlargedCertificates S X z y medium i)}) :
    splitPairFibreOf i (EnlargedCertificates S X z y medium i) c.val =
      splitPairDomain c := by
  ext p
  exact mem_splitPairFibreOf_iff c

/-- Consequently every scalar weight on ordered split pairs has the same
finite sum over the actual fibre and the explicit independent domain. -/
theorem sum_splitPairFibreOf_eq_sum_splitPairDomain
    {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i
      (EnlargedCertificates S X z y medium i)})
    (w : ℕ × ℕ → ℝ) :
    (∑ p ∈ splitPairFibreOf i (EnlargedCertificates S X z y medium i) c.val,
      w p) = ∑ p ∈ splitPairDomain c, w p := by
  rw [splitPairFibreOf_eq_splitPairDomain c]

end Erdos387Proof.ConvenientSplitFibre
