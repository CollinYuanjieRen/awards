import Erdos387Proof.SeparatedCertificateCover
import Erdos387Proof.ConvenientPhaseData

/-! Nonnegative prime-to-rough enlargement with a genuine original anchor.
The full complementary vector, selected small factor, and selected-prime
dyadic block are fixed by the anchor. Source decompositions are existential
provenance, not multiplicity-bearing indices. -/

set_option autoImplicit false

namespace Erdos387Proof.SeparatedCertificateEnlargement

open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open MediumComplementGrouping ConvenientComplementGrouping SeparatedCertificatePhase
open scoped BigOperators

/-- Fixed data used by the single-variable phase estimate. The logarithm
of q-1 indexes the exact open-left, closed-right phase interval. -/
def SameAnchorKey {B K X : ℕ} {S : BPZSection6Input B K} (i : Fin S.k)
    (a e : SplitCertificate S X) : Prop :=
  vector i a.1 = vector i e.1 ∧ a.2.1 = e.2.1 ∧
    Nat.log2 (a.2.2-1) = Nat.log2 (e.2.2-1)

structure Admissible {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium second gap : ℕ) (i : Fin S.k) (t : SplitCertificate S X) : Prop where
  upper : t.1.val.value ≤ X
  near : X/2 < B*t.1.val.value
  factor : t.1.val.factor i = t.2.1*t.2.2
  small : t.2.1 ≤ y^3
  prime_rough : IsZRough y t.2.2
  selected_coprime : Nat.Coprime t.2.1 t.2.2
  small_squarefree : Squarefree t.2.1
  factors : ∀ a, t.1.val.factor a ≤ medium ∧ IsZRough z (t.1.val.factor a) ∧
    (a ≠ i → Squarefree (t.1.val.factor a))
  anchor : ∃ e ∈ SeparatedCertificateCover.certificates S X z y medium second gap i,
    SameAnchorKey i t e

noncomputable def certificates {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium second gap : ℕ) (i : Fin S.k) : Finset (SplitCertificate S X) := by
  classical
  exact (Finset.univ.product ((Finset.Icc 1 X).product (Finset.Ioc 1 X))).filter
    (Admissible S X z y medium second gap i)

theorem admissible {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    Admissible S X z y medium second gap i t := by
  classical
  exact (Finset.mem_filter.mp ht).2

/-- Only a nonnegative counting family is enlarged. In particular r and
q remain coprime even though the prime condition on q is dropped. -/
theorem original_subset {B K X z y medium second gap : ℕ} (S : BPZSection6Input B K)
    (hz : 2*S.k ≤ z) (hsecond : 1 ≤ second) (i : Fin S.k) :
    SeparatedCertificateCover.certificates S X z y medium second gap i ⊆
      certificates S X z y medium second gap i := by
  classical
  intro t ht
  have hb := SeparatedCertificateCover.split_bounds ht
  have hg := SeparatedCertificateCover.geometry ht
  have hq := SeparatedCertificateCover.selected_prime hsecond ht
  have hf := SeparatedCertificateCover.factor_eq ht
  have hsq := SeparatedCertificateCover.factor_squarefree ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hb.1,hb.2.1⟩,Finset.mem_Ioc.mpr ⟨hq.1.one_lt,hb.2.2.2.1⟩⟩⟩,?_⟩
  exact { upper := hg.1, near := hg.2.1, factor := hf, small := hb.2.2.2.2
          prime_rough := SeparatedCertificateCover.selected_prime_rough hsecond ht
          selected_coprime := SeparatedCertificateCover.selected_coprime ht
          small_squarefree := (Nat.squarefree_mul_iff.mp (hf ▸ hsq i)).2.1
          factors := fun a => ⟨hg.2.2 a,SeparatedCertificateCover.factor_rough hz ht a,fun _ => hsq a⟩
          anchor := ⟨t,ht,rfl,rfl,rfl⟩ }

theorem card_inter_le_sum_classes {B K X z y medium second gap : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k ≤ z) (hsecond : 1 ≤ second) :
    (RefinedSquarefreeCandidates S X z ∩
      RefinedSeparatedAlmostPrimeErrors S X z y medium second gap).card ≤
      ∑ i : Fin S.k, ∑ t ∈ certificates S X z y medium second gap i,
        (MediumCertificateCover.siftedClass t.1 z).card := by
  classical
  apply (SeparatedCertificateCover.card_inter_le_sum_classes S hz hsecond).trans
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.sum_le_sum_of_subset (original_subset S hz hsecond i)

theorem split_bounds {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    1 ≤ t.2.1 ∧ t.2.1 ≤ X ∧ 1 < t.2.2 ∧ t.2.2 ≤ X := by
  classical
  have hh := Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2
  exact ⟨(Finset.mem_Icc.mp hh.1).1,(Finset.mem_Icc.mp hh.1).2,
    (Finset.mem_Ioc.mp hh.2).1,(Finset.mem_Ioc.mp hh.2).2⟩

/-- The retained tuple constraints also lie in the already proved generic
split enlargement at cutoff0; this reuses its complement and rough-unit
lemmas without imposing the convenient-error splitting threshold. -/
theorem mem_generic_split_enlargement {B K X z y medium second gap : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    t ∈ ConvenientCertificateEnlargement.certificates S X z 0 medium i := by
  classical
  have hb := split_bounds ht
  have ha := admissible ht
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
    ⟨Finset.mem_Ioc.mpr ⟨by omega,hb.2.1⟩,Finset.mem_Ioc.mpr ⟨by omega,hb.2.2.2⟩⟩⟩,
    ha.upper,ha.near,ha.factor,ha.factors⟩

/-- The varying rough coordinate remains a unit modulo the exact fixed
conductor g*r*D*M, using the explicitly retained internal r-q coprimality. -/
theorem selected_unit_modulus {B K X z y medium second gap g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i)
    (hg : g ≠ 0) (hsupport : ∀ p ∈ g.primeFactors, p < z) :
    Nat.Coprime t.2.2 (g*t.2.1*t.1.val.otherValue i*refinementModulus S) := by
  have hd := ConvenientCertificateEnlargement.retained_data (mem_generic_split_enlargement ht)
  have hqg := (ConvenientPhaseData.coprime_of_support_rough hg hsupport hd.2.2.2.1).symm
  have hqr := (admissible ht).selected_coprime.symm
  have hqMD := hd.2.2.2.2.2
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hqg.mul_right (hqr.mul_right hqMD)

noncomputable def anchor {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) : SplitCertificate S X :=
  Classical.choose (admissible ht).anchor

theorem anchor_mem {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    anchor ht ∈ SeparatedCertificateCover.certificates S X z y medium second gap i :=
  (Classical.choose_spec (admissible ht).anchor).1

theorem anchor_key {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) : SameAnchorKey i t (anchor ht) :=
  (Classical.choose_spec (admissible ht).anchor).2

theorem anchor_complement_eq {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i) :
    (anchor ht).1.val.otherValue i = t.1.val.otherValue i := by
  have hh := (vector_eq_iff i t.1 (anchor ht).1).mp (anchor_key ht).1
  unfold TupleCertificate.otherValue
  apply Finset.prod_congr rfl
  intro a ha
  exact (hh a (Finset.mem_erase.mp ha).1).symm

theorem exact_prime_block (q : ℕ) (hq : 1 < q) :
    2^(Nat.log2 (q-1)) < q ∧ q ≤ 2^(Nat.log2 (q-1)+1) := by
  have hp : 0 < q-1 := by omega
  have hb := (Nat.log2_eq_iff hp.ne').mp rfl
  omega

/-- The common full-interval endpoint, including endpoint primes that are
powers of two. -/
def blockUpper (q : ℕ) : ℕ := 2^(Nat.log2 (q-1)+1)

theorem mem_blockIoc (q : ℕ) (hq : 1 < q) : q ∈ Finset.Ioc (blockUpper q/2) (blockUpper q) := by
  have hb := exact_prime_block q hq
  have hhalf : blockUpper q/2 = 2^(Nat.log2 (q-1)) := by
    unfold blockUpper
    rw [pow_succ]
    omega
  exact Finset.mem_Ioc.mpr ⟨by simpa only [hhalf] using hb.1,hb.2⟩

theorem blockUpper_le_twice {q X : ℕ} (hq : 1 < q) (hX : q ≤ X) : blockUpper q ≤ 2*X := by
  have hb := (exact_prime_block q hq).1
  unfold blockUpper
  rw [pow_succ]
  omega

/-- Controlled anchor extraction fixes the removed index and conductor.
The anchor's largest prime is at most the common dyadic endpoint Q. -/
theorem exists_anchor_phase_data {B K X z y medium second gap g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium second gap i)
    (hz : 2*S.k ≤ z) (hsecond : 1 ≤ second) (hgSq : Squarefree g)
    (hgSupport : ∀ p ∈ g.primeFactors, p < z) :
    ∃ (n : ℕ) (C : CertificatePhaseData S n y medium second gap g),
      C.i₀ = i ∧ C.q C.i₀ ≤ blockUpper t.2.2 ∧
      (∀ a, a ≠ i → C.E.factor a = t.1.val.factor a) ∧
      C.modulus = g*t.2.1*t.1.val.otherValue i*refinementModulus S := by
  obtain ⟨C,hi,hq,hf,hmod⟩ := SeparatedCertificateCover.exists_source_phase_data
    (anchor_mem ht) hz hsecond hgSq hgSupport
  refine ⟨_,C,hi,?_,?_,?_⟩
  · rw [hi,hq]
    have hp := (SeparatedCertificateCover.selected_prime hsecond (anchor_mem ht)).1.one_lt
    have hbound := (exact_prime_block (anchor ht).2.2 hp).2
    simpa only [blockUpper,← (anchor_key ht).2.2] using hbound
  · intro a ha
    rw [hf a]
    exact ((vector_eq_iff i t.1 (anchor ht).1).mp (anchor_key ht).1 a ha).symm
  · rw [hmod,anchor_complement_eq ht,← (anchor_key ht).2.1]

/-- Algebraic grouping remains injective after the NONNEGATIVE enlargement. -/
theorem groupingIndex_injOn {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} : Set.InjOn (ConvenientComplementGrouping.groupingIndex i)
      (↑(certificates S X z y medium second gap i) : Set (SplitCertificate S X)) :=
  ConvenientComplementGrouping.groupingIndex_injOn_of_factor _ (fun _ ht => (admissible ht).factor)

end Erdos387Proof.SeparatedCertificateEnlargement
