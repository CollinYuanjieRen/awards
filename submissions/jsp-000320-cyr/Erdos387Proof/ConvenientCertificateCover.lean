import Erdos387Proof.MediumCertificateCover
import ErdosProblems.Erdos387.TupleCoordinateCRT
import Mathlib.Data.Nat.Log

/-! A nonnegative cover of the original convenient error by independent
split certificates and an exact finite dyadic partition. All roughness,
squarefreeness, medium bounds, and the near-product window are retained. -/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientCertificateCover

open Erdos387 Erdos387.CoverBPZ
open scoped BigOperators

abbrev SplitCertificate {B K : ℕ} (S : BPZSection6Input B K) (X : ℕ) :=
  RefinedTupleCertificate S X × (ℕ × ℕ)

noncomputable def certificates {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium : ℕ) (i : Fin S.k) : Finset (SplitCertificate S X) := by
  classical
  exact (Finset.univ.product ((Finset.Ioc y X).product (Finset.Ioc y X))).filter fun t =>
    t.1.val.value ≤ X ∧ X/2 < B*t.1.val.value ∧ t.1.val.factor i = t.2.1*t.2.2 ∧
      ∀ j, t.1.val.factor j ≤ medium ∧ Squarefree (t.1.val.factor j) ∧
        IsZRough z (t.1.val.factor j)

theorem exists_certificate {B K X z y medium n : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k ≤ z)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (hnErr : n ∈ RefinedConvenientErrors S X z y medium) :
    ∃ (i : Fin S.k) (t : SplitCertificate S X),
      t ∈ certificates S X z y medium i ∧
        n ∈ MediumCertificateCover.siftedClass t.1 z := by
  classical
  obtain ⟨_, hnErr⟩ := Finset.mem_filter.mp hnErr
  obtain ⟨hn, hprog, d, E, hnear, hdn, hvalue, hconv, hmedium⟩ := hnErr
  obtain ⟨i,r,s, hrs, hyr,hys⟩ := hconv
  have hnData := hnSq
  rw [RefinedSquarefreeCandidates, Finset.mem_filter,
    RefinedSiftedCandidates, Finset.mem_filter, mem_RefinedBaseCandidates] at hnData
  have hnIoc := hnData.1.1.1
  have hvaln : E.value ≤ n := hvalue.trans_le hdn
  have hvalX : E.value ≤ X := hvaln.trans (Finset.mem_Ioc.mp hnIoc).2
  have hnearE : n < B*E.value := by simpa only [hvalue] using hnear
  obtain ⟨hfactorSq,hvalueSq,_⟩ := coverDivisorTuple_squarefree_data S hnSq hn hprog E
  obtain ⟨hMvalue,hvalueRough⟩ := coverDivisorTuple_rough_data S hnSq hn hprog E hz
  have hdvd (j : Fin S.k) : E.factor j ∣ E.value :=
    Finset.dvd_prod_of_mem E.factor (Finset.mem_univ j)
  have hpos (j : Fin S.k) : 0 < E.factor j := Nat.pos_of_ne_zero (hfactorSq j).ne_zero
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
  let C : RefinedTupleCertificate S X := ⟨C₀,hMvalue⟩
  have hr : r ∈ Finset.Ioc y X := by
    apply Finset.mem_Ioc.mpr
    refine ⟨hyr, ?_⟩
    have := hfactorX i
    rw [hrs] at this
    exact (Nat.le_mul_of_pos_right r (by omega : 0 < s)).trans this
  have hs : s ∈ Finset.Ioc y X := by
    apply Finset.mem_Ioc.mpr
    refine ⟨hys, ?_⟩
    have := hfactorX i
    rw [hrs] at this
    exact (Nat.le_mul_of_pos_left s (by omega : 0 < r)).trans this
  refine ⟨i,(C,r,s), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨hr,hs⟩⟩,
      hvalX, (Finset.mem_Ioc.mp hnIoc).1.trans hnearE, hrs, ?_⟩
    intro j
    refine ⟨hmedium j,hfactorSq j,?_⟩
    intro p hp hpz hpj
    have hpval : p ∈ E.value.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp,hpj.trans (hdvd j),hvalueSq.ne_zero⟩
    exact (not_lt_of_ge (hvalueRough p hpval)) hpz
  · apply Finset.mem_filter.mpr
    refine ⟨?_,(Finset.mem_filter.mp hnSq).1⟩
    apply (RefinedTupleCertificate.mem_classIoc_iff C).mpr
    refine ⟨hnIoc,(refinement_progression_dvd_iff_modEq S).mp hnData.1.1.2.2,?_⟩
    apply C₀.ambient_modEq_crtResidue hn.le hvaln
    intro j
    exact (E.divides j).trans
      (coverQuotient_dvd_term (S.toCoverFactorization hn hprog) j.isLt)

/-- This union bound is applied only to the nonnegative original class
counts, before a signed sieve expansion. -/
theorem card_inter_le_sum_classes {B K X z y medium : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k ≤ z) :
    (RefinedSquarefreeCandidates S X z ∩ RefinedConvenientErrors S X z y medium).card ≤
      ∑ i : Fin S.k, ∑ t ∈ certificates S X z y medium i,
        (MediumCertificateCover.siftedClass t.1 z).card := by
  classical
  let U := (Finset.univ : Finset (Fin S.k)).biUnion fun i =>
    (certificates S X z y medium i).biUnion fun t => MediumCertificateCover.siftedClass t.1 z
  have hsub : RefinedSquarefreeCandidates S X z ∩
      RefinedConvenientErrors S X z y medium ⊆ U := by
    intro n hn
    obtain ⟨i,t,ht,hnT⟩ := exists_certificate S hz (Finset.mem_inter.mp hn).1 (Finset.mem_inter.mp hn).2
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨t,ht,hnT⟩⟩
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.card_biUnion_le

theorem split_geometry {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium i) :
    0 < t.1.val.otherValue i ∧ t.1.val.otherValue i ≤ X ∧
      y < t.2.1 ∧ t.2.1 ≤ X ∧ y < t.2.2 ∧ t.2.2 ≤ X ∧
      t.1.val.otherValue i * t.2.1 * t.2.2 = t.1.val.value ∧
      t.2.1*t.2.2 ≤ medium ∧ X/2 < B*(t.1.val.otherValue i*t.2.1*t.2.2) ∧
      t.1.val.otherValue i*t.2.1*t.2.2 ≤ X := by
  classical
  obtain ⟨ht0,hX,hnear,hrs,hf⟩ := Finset.mem_filter.mp ht
  obtain ⟨hr,hs⟩ := Finset.mem_product.mp (Finset.mem_product.mp ht0).2
  have hDpos : 0 < t.1.val.otherValue i :=
    Finset.prod_pos (fun j _ => t.1.val.positive j)
  have hprod : t.1.val.otherValue i*t.2.1*t.2.2 = t.1.val.value := by
    rw [← t.1.val.factor_mul_otherValue i, hrs]
    ring
  have hDX : t.1.val.otherValue i ≤ X :=
    (Nat.le_of_dvd t.1.val.value_pos (by rw [← t.1.val.factor_mul_otherValue i]; exact dvd_mul_left _ _)).trans hX
  exact ⟨hDpos,hDX,(Finset.mem_Ioc.mp hr).1,(Finset.mem_Ioc.mp hr).2,
    (Finset.mem_Ioc.mp hs).1,(Finset.mem_Ioc.mp hs).2,hprod,
    hrs ▸ (hf i).1,by simpa only [hprod] using hnear,by simpa only [hprod] using hX⟩


theorem complement_bounds {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (hB : 0 < B) (ht : t ∈ certificates S X z y medium i) :
    (X/2)/(B*medium) < t.1.val.otherValue i ∧
      t.1.val.otherValue i ≤ X/(y+1)^2 := by
  obtain ⟨hD,hDX,hr,hrX,hs,hsX,hprod,hrs,hnear,hupper⟩ := split_geometry ht
  have hmed : 0 < medium := (Nat.mul_pos (by omega : 0 < t.2.1)
    (by omega : 0 < t.2.2)).trans_le hrs
  constructor
  · apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hB hmed)).mpr
    calc
      X/2 < B*(t.1.val.otherValue i*t.2.1*t.2.2) := hnear
      _ ≤ t.1.val.otherValue i*(B*medium) := by nlinarith [Nat.mul_le_mul_left (B*t.1.val.otherValue i) hrs]
  · apply (Nat.le_div_iff_mul_le (by positivity : 0 < (y+1)^2)).mpr
    calc
      _ ≤ t.1.val.otherValue i*(t.2.1*t.2.2) := by
        apply Nat.mul_le_mul_left
        simpa only [pow_two] using Nat.mul_le_mul (Nat.succ_le_of_lt hr) (Nat.succ_le_of_lt hs)
      _ ≤ X := by simpa only [Nat.mul_assoc] using hupper

/-- Roughness and squarefreeness are retained on both split variables and
on the complementary product, so the small sieve primes are disjoint. -/
theorem split_regular {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium i) :
    Squarefree t.2.1 ∧ Squarefree t.2.2 ∧ Squarefree (t.1.val.otherValue i) ∧
      IsZRough z t.2.1 ∧ IsZRough z t.2.2 ∧ IsZRough z (t.1.val.otherValue i) ∧
      t.2.1.Coprime t.2.2 ∧ (t.2.1*t.2.2).Coprime (t.1.val.otherValue i) := by
  classical
  obtain ⟨_,_,_,hrs,hf⟩ := Finset.mem_filter.mp ht
  have hsq : Squarefree (t.2.1*t.2.2) := hrs ▸ (hf i).2.1
  have hrough : IsZRough z (t.2.1*t.2.2) := hrs ▸ (hf i).2.2
  have hDsq : Squarefree (t.1.val.otherValue i) := by
    unfold TupleCertificate.otherValue
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro a _ b _ hab
      change IsRelPrime (t.1.val.factor a) (t.1.val.factor b)
      rw [← Nat.coprime_iff_isRelPrime]
      exact t.1.val.pairwise a b hab
    · intro j _
      exact (hf j).2.1
  have hDrough : IsZRough z (t.1.val.otherValue i) := by
    intro p hp hpz hpd
    obtain ⟨j,hj,hpj⟩ := (hp.prime.dvd_finsetProd_iff t.1.val.factor).mp hpd
    exact (hf j).2.2 p hp hpz hpj
  exact ⟨hsq.squarefree_of_dvd (dvd_mul_right _ _),
    hsq.squarefree_of_dvd (dvd_mul_left _ _),hDsq,
    (fun p hp hpz hpr => hrough p hp hpz (hpr.trans (dvd_mul_right _ _))),
    (fun p hp hpz hps => hrough p hp hpz (hps.trans (dvd_mul_left _ _))),
    hDrough,Nat.coprime_of_squarefree_mul hsq,
    hrs ▸ t.1.val.factor_coprime_otherValue i⟩

def dyadicIndices (X : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.range (Nat.log 2 X+1)).product
    ((Finset.range (Nat.log 2 X+1)).product (Finset.range (Nat.log 2 X+1)))

theorem card_dyadicIndices (X : ℕ) :
    (dyadicIndices X).card = (Nat.log 2 X+1)^3 := by
  simp only [dyadicIndices,Finset.product_eq_sprod,Finset.card_product,Finset.card_range]
  ring

def dyadicLabel {B K X : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (t : SplitCertificate S X) : ℕ × (ℕ × ℕ) :=
  (Nat.log 2 (t.1.val.otherValue i),Nat.log 2 t.2.1,Nat.log 2 t.2.2)

noncomputable def boxedCertificates {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium : ℕ) (i : Fin S.k) (a : ℕ × (ℕ × ℕ)) :
    Finset (SplitCertificate S X) := by
  classical
  exact (certificates S X z y medium i).filter (fun t => dyadicLabel i t = a)

theorem label_mem {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium i) : dyadicLabel i t ∈ dyadicIndices X := by
  classical
  have h := split_geometry ht
  simp only [dyadicLabel,dyadicIndices,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) h.2.1),
    Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) h.2.2.2.1),
    Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) h.2.2.2.2.2.1)⟩

theorem mem_dyadic_interval {n : ℕ} (hn : 0 < n) :
    n ∈ Finset.Ico (2^(Nat.log 2 n)) (2^(Nat.log 2 n+1)) := by
  exact Finset.mem_Ico.mpr ⟨Nat.pow_log_le_self 2 hn.ne',Nat.lt_pow_succ_log_self (by norm_num) n⟩


theorem boxed_intervals {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X} {a : ℕ × (ℕ × ℕ)}
    (ht : t ∈ boxedCertificates S X z y medium i a) :
    t.1.val.otherValue i ∈ Finset.Ico (2^a.1) (2^(a.1+1)) ∧
      t.2.1 ∈ Finset.Ico (2^a.2.1) (2^(a.2.1+1)) ∧
      t.2.2 ∈ Finset.Ico (2^a.2.2) (2^(a.2.2+1)) := by
  classical
  obtain ⟨ht,hlabel⟩ := Finset.mem_filter.mp ht
  have h := split_geometry ht
  have he : Nat.log 2 (t.1.val.otherValue i) = a.1 := congrArg Prod.fst hlabel
  have hf : Nat.log 2 t.2.1 = a.2.1 := congrArg (fun v => v.2.1) hlabel
  have hg : Nat.log 2 t.2.2 = a.2.2 := congrArg (fun v => v.2.2) hlabel
  exact ⟨by simpa only [he] using mem_dyadic_interval h.1,
    by simpa only [hf] using mem_dyadic_interval ((Nat.zero_le y).trans_lt h.2.2.1),
    by simpa only [hg] using mem_dyadic_interval ((Nat.zero_le y).trans_lt h.2.2.2.2.1)⟩

/-- The partition is exact, so it loses neither a certificate nor a
factorization, and never identifies distinct complementary tuples. -/
theorem sum_boxed_eq {B K X z y medium : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (w : SplitCertificate S X → ℕ) :
    (∑ a ∈ dyadicIndices X, ∑ t ∈ boxedCertificates S X z y medium i a, w t) =
      ∑ t ∈ certificates S X z y medium i, w t := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (fun _ ht => label_mem ht) w

theorem card_inter_le_sum_boxed_classes {B K X z y medium : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k ≤ z) :
    (RefinedSquarefreeCandidates S X z ∩ RefinedConvenientErrors S X z y medium).card ≤
      ∑ i : Fin S.k, ∑ a ∈ dyadicIndices X,
        ∑ t ∈ boxedCertificates S X z y medium i a,
          (MediumCertificateCover.siftedClass t.1 z).card := by
  simp_rw [sum_boxed_eq]
  exact card_inter_le_sum_classes S hz

end Erdos387Proof.ConvenientCertificateCover
