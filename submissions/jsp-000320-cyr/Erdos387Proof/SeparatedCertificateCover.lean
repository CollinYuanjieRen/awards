import Erdos387Proof.ConvenientComplementGrouping
import Erdos387Proof.SeparatedCertificatePhase

/-! A finite cover by actual separated split certificates. The original
factorization and squarefree integer witness occur only as existential
provenance, never as an additional summation index. Consequently the same
(complement,r,q) grouping used for split certificates is injective here. -/

set_option autoImplicit false

namespace Erdos387Proof.SeparatedCertificateCover

open Erdos387 Erdos387.CoverBPZ
open ConvenientCertificateCover MediumComplementGrouping ConvenientComplementGrouping
open SeparatedCertificatePhase
open scoped BigOperators

/-- Provenance of one original separated split certificate. None of the
complementary small factors is required to be smooth. -/
structure SourceWitness {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium second gap : ℕ) (i : Fin S.k) (t : SplitCertificate S X) where
  n : ℕ
  n_mem : n ∈ RefinedSquarefreeCandidates S X z
  hn : S.k < n
  hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ)-S.α
  E : CoverDivisorTuple (S.toCoverFactorization hn hprog)
  f : Fin S.k → ℕ
  q : Fin S.k → ℕ
  j : Fin S.k
  near : n < B*E.value
  upper : E.value ≤ n
  factors : ∀ a, t.1.val.factor a = E.factor a
  selected_small : t.2.1 = f i
  selected_prime : t.2.2 = q i
  factor : ∀ a, E.factor a = f a*q a
  small : ∀ a, f a ≤ y^3
  shape : ∀ a, q a = 1 ∨ (q a).Prime ∧ y < q a
  medium_bound : ∀ a, E.factor a ≤ medium
  largest : ∀ a, q a ≤ q i
  distinct : i ≠ j
  second_large : second < q j
  separated : ∀ a, a ≠ i → gap*q a ≤ q i

noncomputable def certificates {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium second gap : ℕ) (i : Fin S.k) : Finset (SplitCertificate S X) := by
  classical
  exact (Finset.univ.product ((Finset.Icc 1 X).product (Finset.Ioc y X))).filter fun t =>
    Nonempty (SourceWitness S X z y medium second gap i t)

noncomputable def source {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    SourceWitness S X z y medium second gap i t := by
  classical
  exact Classical.choice (Finset.mem_filter.mp ht).2

/-- Original separated errors supply a finite split certificate with all
source information retained, but without summing over decompositions. -/
theorem exists_certificate {B K X z y medium second gap n : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k ≤ z) (hsecond : 1 ≤ second)
    (hnSq : n ∈ RefinedSquarefreeCandidates S X z)
    (hnErr : n ∈ RefinedSeparatedAlmostPrimeErrors S X z y medium second gap) :
    ∃ (i : Fin S.k) (t : SplitCertificate S X),
      t ∈ certificates S X z y medium second gap i ∧
        n ∈ MediumCertificateCover.siftedClass t.1 z := by
  classical
  obtain ⟨_,hnErr⟩ := Finset.mem_filter.mp hnErr
  obtain ⟨hn,hprog,d,E,f,q,i,j,hnear,hdn,hvalue,hfactor,hsmall,hshape,
    hmedium,hlargest,hij,hsecondj,hgap⟩ := hnErr
  have hnData := hnSq
  rw [RefinedSquarefreeCandidates,Finset.mem_filter,RefinedSiftedCandidates,
    Finset.mem_filter,mem_RefinedBaseCandidates] at hnData
  have hnIoc := hnData.1.1.1
  have hvaln : E.value ≤ n := hvalue.trans_le hdn
  have hvalX : E.value ≤ X := hvaln.trans (Finset.mem_Ioc.mp hnIoc).2
  have hnearE : n < B*E.value := by simpa only [hvalue] using hnear
  obtain ⟨hfactorSq,hvalueSq,_⟩ := coverDivisorTuple_squarefree_data S hnSq hn hprog E
  obtain ⟨hMvalue,_⟩ := coverDivisorTuple_rough_data S hnSq hn hprog E hz
  have hdvd (a : Fin S.k) : E.factor a ∣ E.value :=
    Finset.dvd_prod_of_mem E.factor (Finset.mem_univ a)
  have hpos (a : Fin S.k) : 0 < E.factor a := Nat.pos_of_ne_zero (hfactorSq a).ne_zero
  have hfactorX (a : Fin S.k) : E.factor a ≤ X :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hvalueSq.ne_zero) (hdvd a)).trans hvalX
  have hpair (a b : Fin S.k) (hab : a ≠ b) : Nat.Coprime (E.factor a) (E.factor b) :=
    Nat.Coprime.of_dvd_right (E.divides b)
      (Nat.Coprime.of_dvd_left (E.divides a)
        (S.coverQuotients_pairwise_coprime hn hprog
          a a.isLt b b.isLt (fun h => hab (Fin.ext h))))
  let C₀ : TupleCertificate S.k X :=
    ⟨fun a => ⟨E.factor a, by have := hfactorX a; omega⟩,hpos,hpair⟩
  let C : RefinedTupleCertificate S X := ⟨C₀,hMvalue⟩
  have hqi : 1 < q i := lt_of_lt_of_le (hsecond.trans_lt hsecondj) (hlargest j)
  have hprime : (q i).Prime ∧ y < q i := (hshape i).resolve_left (by omega)
  have hfi : 0 < f i := by
    have hp := hpos i
    rw [hfactor i] at hp
    by_contra hn
    have hf0 : f i = 0 := by omega
    simp only [hf0,zero_mul,lt_self_iff_false] at hp
  have hsplitX : f i*q i ≤ X := (hfactor i) ▸ hfactorX i
  have hfX : f i ≤ X := (Nat.le_mul_of_pos_right _ (by omega : 0<q i)).trans hsplitX
  have hqX : q i ≤ X := (Nat.le_mul_of_pos_left _ hfi).trans hsplitX
  refine ⟨i,(C,f i,q i),?_,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hfi,hfX⟩,Finset.mem_Ioc.mpr ⟨hprime.2,hqX⟩⟩⟩,?_⟩
    exact ⟨{ n := n, n_mem := hnSq, hn := hn, hprog := hprog, E := E, f := f, q := q, j := j
             near := hnearE, upper := hvaln, factors := fun _ => rfl,
             selected_small := rfl, selected_prime := rfl, factor := hfactor,
             small := hsmall, shape := hshape, medium_bound := hmedium,
             largest := hlargest, distinct := hij, second_large := hsecondj, separated := hgap }⟩
  · apply Finset.mem_filter.mpr
    refine ⟨?_,(Finset.mem_filter.mp hnSq).1⟩
    apply (RefinedTupleCertificate.mem_classIoc_iff C).mpr
    refine ⟨hnIoc,(refinement_progression_dvd_iff_modEq S).mp hnData.1.1.2.2,?_⟩
    apply C₀.ambient_modEq_crtResidue hn.le hvaln
    intro a
    exact (E.divides a).trans (coverQuotient_dvd_term (S.toCoverFactorization hn hprog) a.isLt)

/-- This nonnegative union bound precedes all signed Fourier/sieve
expansions. Existential witnesses are not counted as extra indices. -/
theorem card_inter_le_sum_classes {B K X z y medium second gap : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k ≤ z) (hsecond : 1 ≤ second) :
    (RefinedSquarefreeCandidates S X z ∩
      RefinedSeparatedAlmostPrimeErrors S X z y medium second gap).card ≤
      ∑ i : Fin S.k, ∑ t ∈ certificates S X z y medium second gap i,
        (MediumCertificateCover.siftedClass t.1 z).card := by
  classical
  let U := (Finset.univ : Finset (Fin S.k)).biUnion fun i =>
    (certificates S X z y medium second gap i).biUnion fun t =>
      MediumCertificateCover.siftedClass t.1 z
  have hsub : RefinedSquarefreeCandidates S X z ∩
      RefinedSeparatedAlmostPrimeErrors S X z y medium second gap ⊆ U := by
    intro n hn
    obtain ⟨i,t,ht,hnT⟩ := exists_certificate S hz hsecond
      (Finset.mem_inter.mp hn).1 (Finset.mem_inter.mp hn).2
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨t,ht,hnT⟩⟩
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.card_biUnion_le

theorem factor_eq {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    t.1.val.factor i = t.2.1*t.2.2 := by
  let W := source ht
  rw [W.factors i,W.factor i,← W.selected_small,← W.selected_prime]

theorem split_bounds {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    1 ≤ t.2.1 ∧ t.2.1 ≤ X ∧ y < t.2.2 ∧ t.2.2 ≤ X ∧ t.2.1 ≤ y^3 := by
  classical
  have hm := Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2
  have hr := Finset.mem_Icc.mp hm.1
  have hq := Finset.mem_Ioc.mp hm.2
  let W := source ht
  refine ⟨hr.1,hr.2,hq.1,hq.2,?_⟩
  rw [W.selected_small]
  exact W.small i

theorem factor_squarefree {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    ∀ a, Squarefree (t.1.val.factor a) := by
  let W := source ht
  intro a
  rw [W.factors a]
  exact (coverDivisorTuple_squarefree_data S W.n_mem W.hn W.hprog W.E).1 a

/-- Internal selected-factor coprimality is retained explicitly. Tuple
coprimality with the complement alone would not imply this condition. -/
theorem selected_coprime {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) : Nat.Coprime t.2.1 t.2.2 := by
  exact Nat.coprime_of_squarefree_mul (factor_eq ht ▸ factor_squarefree ht i)

theorem value_eq_source {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    t.1.val.value = (source ht).E.value := by
  unfold TupleCertificate.value CoverDivisorTuple.value
  apply Finset.prod_congr rfl
  intro a ha
  exact (source ht).factors a

theorem geometry {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    t.1.val.value ≤ X ∧ X/2 < B*t.1.val.value ∧ ∀ a, t.1.val.factor a ≤ medium := by
  classical
  let W := source ht
  have hnData := W.n_mem
  rw [RefinedSquarefreeCandidates,Finset.mem_filter,RefinedSiftedCandidates,
    Finset.mem_filter,mem_RefinedBaseCandidates] at hnData
  have hnioc := Finset.mem_Ioc.mp hnData.1.1.1
  refine ⟨?_,?_,?_⟩
  · rw [value_eq_source ht]
    exact W.upper.trans hnioc.2
  · rw [value_eq_source ht]
    exact hnioc.1.trans W.near
  · intro a
    rw [W.factors a]
    exact W.medium_bound a

theorem factor_rough {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (hz : 2*S.k ≤ z) (ht : t ∈ certificates S X z y medium second gap i) :
    ∀ a, IsZRough z (t.1.val.factor a) := by
  let W := source ht
  have hsq := (coverDivisorTuple_squarefree_data S W.n_mem W.hn W.hprog W.E).2.1
  have hrough := (coverDivisorTuple_rough_data S W.n_mem W.hn W.hprog W.E hz).2
  intro a p hp hpz hpd
  rw [W.factors a] at hpd
  have hdvd : W.E.factor a ∣ W.E.value :=
    Finset.dvd_prod_of_mem W.E.factor (Finset.mem_univ a)
  have hmem := Nat.mem_primeFactors.mpr ⟨hp,hpd.trans hdvd,hsq.ne_zero⟩
  exact (not_lt_of_ge (hrough p hmem)) hpz

theorem selected_prime {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (hsecond : 1 ≤ second) (ht : t ∈ certificates S X z y medium second gap i) :
    t.2.2.Prime ∧ y < t.2.2 := by
  let W := source ht
  have hlarge : 1 < W.q i := (hsecond.trans_lt W.second_large).trans_le (W.largest W.j)
  rw [W.selected_prime]
  exact (W.shape i).resolve_left (by omega)

theorem selected_prime_rough {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (hsecond : 1 ≤ second) (ht : t ∈ certificates S X z y medium second gap i) :
    IsZRough y t.2.2 := by
  obtain ⟨hq,hqy⟩ := selected_prime hsecond ht
  intro p hp hpy hpd
  rcases (Nat.dvd_prime hq).mp hpd with hp1 | hpeq
  · exact hp.ne_one hp1
  · omega

/-- The existing generic grouping map is injective on the actual family.
No f/q decomposition multiplicity survives in this finite index. -/
theorem groupingIndex_injOn {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} : Set.InjOn (ConvenientComplementGrouping.groupingIndex i)
      (↑(certificates S X z y medium second gap i) : Set (SplitCertificate S X)) :=
  ConvenientComplementGrouping.groupingIndex_injOn_of_factor _ (fun _ ht => factor_eq ht)

/-- Controlled extraction for a chosen finite source certificate: the
removed coordinate and prime are fixed, and the conductor is exactly the
key-dependent g*r*D*M. This is what lets an original fibre anchor govern
an enlarged rough-prime variable without depending on its decomposition. -/
theorem exists_source_phase_data {B K X z y medium second gap g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i)
    (hz : 2*S.k ≤ z) (hsecond : 1 ≤ second) (hgSq : Squarefree g)
    (hgSupport : ∀ p ∈ g.primeFactors, p < z) :
    ∃ C : CertificatePhaseData S (source ht).n y medium second gap g,
      C.i₀ = i ∧ C.q i = t.2.2 ∧ (∀ a, C.E.factor a = t.1.val.factor a) ∧
      C.modulus = g*t.2.1*t.1.val.otherValue i*refinementModulus S := by
  let W := source ht
  obtain ⟨j,ss,hji,hpj,hsecondp,hgapj,hkp,hlen,hprod,hsq,hchain,hmax⟩ :=
    separated_tuple_phase_data S W.n_mem W.hn W.hprog W.E W.f W.q i W.j W.factor
      (fun a => (W.shape a).imp_right And.left) W.distinct hsecond W.second_large
      W.separated hz hgSq hgSupport
  let C : CertificatePhaseData S W.n y medium second gap g :=
    { hn := W.hn, hprog := W.hprog, E := W.E, f := W.f, q := W.q, i₀ := i, j := j, ss := ss
      near := W.near, upper := W.upper, factor := W.factor, small := W.small,
      shape := W.shape, medium_bound := W.medium_bound, largest := W.largest,
      value_squarefree := (coverDivisorTuple_squarefree_data S W.n_mem W.hn W.hprog W.E).2.1,
      terminal_ne := hji, terminal_prime := hpj, terminal_large := hsecondp,
      terminal_gap := hgapj, index_bound := hkp, depth := hlen, remaining := hprod,
      remaining_squarefree := hsq, chain := hchain, remaining_max := hmax }
  refine ⟨C,rfl,W.selected_prime.symm,fun a => (W.factors a).symm,?_⟩
  have hqpos : 0 < W.q i := by
    rw [← W.selected_prime]
    exact (Nat.zero_le y).trans_lt (split_bounds ht).2.2.1
  apply Nat.eq_of_mul_eq_mul_right hqpos
  have hrem := C.modulus_mul_removed
  change C.modulus*W.q i = g*W.E.value*refinementModulus S at hrem
  calc
    _ = g*W.E.value*refinementModulus S := hrem
    _ = _ := by
      rw [← value_eq_source ht,← t.1.val.factor_mul_otherValue i,factor_eq ht,W.selected_prime]
      ring

end Erdos387Proof.SeparatedCertificateCover
