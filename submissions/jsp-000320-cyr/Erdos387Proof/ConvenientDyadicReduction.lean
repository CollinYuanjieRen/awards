import Erdos387Proof.ConvenientMomentBoxes

/-!
# Exact dyadic reduction for enlarged convenient certificates

The enlarged convenient family is indexed first by its complementary vector
and then by an ordered split pair.  This file partitions that exact nested
finite domain by the three dyadic logarithms.  In particular, `boxedPairs`
is a filter of `splitPairDomain`, so all roughness, unit, medium, and product
masks remain present after the partition.
-/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientDyadicReduction

open Erdos387 Erdos387.CoverBPZ
open ConvenientCertificateCover ConvenientComplementGrouping
open ConvenientSplitFibre ConvenientMomentBoxes
open scoped BigOperators

/-- The actual enlarged complement/split-pair domain, kept as a dependent
finite sigma type so the complement remains the outer index. -/
noncomputable def complementPairs {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium : ℕ) (i : Fin S.k) :
    Finset (Σ c : Index S X z y medium i, ℕ × ℕ) := by
  classical
  exact (complementVectorsOf i
    (EnlargedCertificates S X z y medium i)).attach.sigma splitPairDomain

/-- The three dyadic logarithms of a complementary product and its ordered
split pair. -/
def dyadicLabel {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (t : Σ c : Index S X z y medium i, ℕ × ℕ) :
    ℕ × (ℕ × ℕ) :=
  (Nat.log 2 (product t.1), Nat.log 2 t.2.1, Nat.log 2 t.2.2)

/-- The exact split-pair fibre inside a fixed pair of dyadic intervals.
Since this filters `splitPairDomain`, none of its arithmetic masks is lost. -/
noncomputable def boxedPairs {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : Index S X z y medium i) (r s : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (splitPairDomain c).filter fun p =>
    p.1 ∈ Finset.Ico (2^r) (2^(r+1)) ∧
      p.2 ∈ Finset.Ico (2^s) (2^(s+1))

theorem mem_boxedPairs_iff {B K X z y medium r s : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    {c : Index S X z y medium i} {p : ℕ × ℕ} :
    p ∈ boxedPairs c r s ↔
      p ∈ splitPairDomain c ∧
      p.1 ∈ Finset.Ico (2^r) (2^(r+1)) ∧
      p.2 ∈ Finset.Ico (2^s) (2^(s+1)) := by
  classical
  simp only [boxedPairs, Finset.mem_filter]

theorem label_mem {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    {t : Σ c : Index S X z y medium i, ℕ × ℕ}
    (ht : t ∈ complementPairs S X z y medium i) :
    dyadicLabel t ∈ ConvenientCertificateCover.dyadicIndices X := by
  classical
  obtain ⟨hc,hp⟩ := Finset.mem_sigma.mp ht
  have hD := product_data t.1
  have hpair := (mem_splitPairDomain_iff t.1).mp hp
  simp only [dyadicLabel, ConvenientCertificateCover.dyadicIndices,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) hD.2.1),
    Nat.lt_succ_of_le (Nat.log_mono_right (b := 2)
      (Finset.mem_Ioc.mp hpair.1).2),
    Nat.lt_succ_of_le (Nat.log_mono_right (b := 2)
      (Finset.mem_Ioc.mp hpair.2.1).2)⟩

/-- On the actual domain, equality with a dyadic label is equivalent to the
three interval conditions used by `activeIndices` and `boxedPairs`. -/
theorem dyadicLabel_eq_iff_intervals {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    {c : Index S X z y medium i} {p : ℕ × ℕ}
    (hp : p ∈ splitPairDomain c) (a : ℕ × (ℕ × ℕ)) :
    dyadicLabel (Sigma.mk c p) = a ↔
      product c ∈ Finset.Ico (2^a.1) (2^(a.1+1)) ∧
      p.1 ∈ Finset.Ico (2^a.2.1) (2^(a.2.1+1)) ∧
      p.2 ∈ Finset.Ico (2^a.2.2) (2^(a.2.2+1)) := by
  have hD0 := (product_data c).1
  have hpair := (mem_splitPairDomain_iff c).mp hp
  have hr0 : 0 < p.1 := (Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hpair.1).1
  have hs0 : 0 < p.2 := (Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hpair.2.1).1
  constructor
  · intro h
    have he : Nat.log 2 (product c) = a.1 := congrArg Prod.fst h
    have hr : Nat.log 2 p.1 = a.2.1 := congrArg (fun v => v.2.1) h
    have hs : Nat.log 2 p.2 = a.2.2 := congrArg (fun v => v.2.2) h
    exact ⟨by simpa only [he] using ConvenientCertificateCover.mem_dyadic_interval hD0,
      by simpa only [hr] using ConvenientCertificateCover.mem_dyadic_interval hr0,
      by simpa only [hs] using ConvenientCertificateCover.mem_dyadic_interval hs0⟩
  · rintro ⟨hD,hr,hs⟩
    apply Prod.ext
    · exact Nat.log_eq_of_pow_le_of_lt_pow
        (Finset.mem_Ico.mp hD).1 (Finset.mem_Ico.mp hD).2
    · apply Prod.ext
      · exact Nat.log_eq_of_pow_le_of_lt_pow
          (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2
      · exact Nat.log_eq_of_pow_le_of_lt_pow
          (Finset.mem_Ico.mp hs).1 (Finset.mem_Ico.mp hs).2

/-- The fibre of the global dyadic label is exactly the nested active
complement domain with its exact boxed split-pair fibres. -/
theorem label_fibre_eq_active_sigma {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (a : ℕ × (ℕ × ℕ)) :
    (complementPairs S X z y medium i).filter (fun t => dyadicLabel t = a) =
      (activeIndices S X z y medium i a.1 a.2.1 a.2.2).sigma
        (fun c => boxedPairs c a.2.1 a.2.2) := by
  classical
  ext t
  rw [complementPairs, Finset.mem_filter, Finset.mem_sigma, Finset.mem_sigma]
  constructor
  · rintro ⟨⟨hc,hp⟩,hlabel⟩
    obtain ⟨hD,hr,hs⟩ := (dyadicLabel_eq_iff_intervals hp a).mp hlabel
    refine ⟨Finset.mem_filter.mpr ⟨hc,hD,?_⟩,
      (mem_boxedPairs_iff).mpr ⟨hp,hr,hs⟩⟩
    exact ⟨t.2,hp,hr,hs⟩
  · rintro ⟨hc,hpbox⟩
    obtain ⟨hc0,hD,_⟩ := Finset.mem_filter.mp hc
    obtain ⟨hp,hr,hs⟩ := (mem_boxedPairs_iff).mp hpbox
    exact ⟨⟨hc0,hp⟩,(dyadicLabel_eq_iff_intervals hp a).mpr ⟨hD,hr,hs⟩⟩

/-- Exact enlarged-family dyadic partition.  The left side is the original
complement-only outer sum with its complete masked split-pair fibre.  The
right side first chooses the three dyadic scales, then an active complement,
and only then an ordered pair in the exact boxed fibre. -/
theorem sum_eq_sum_dyadic
    {B K X z y medium : ℕ} {S : BPZSection6Input B K} (i : Fin S.k)
    {A : Type*} [AddCommMonoid A]
    (w : (Σ c : Index S X z y medium i, ℕ × ℕ) → A) :
    (∑ c ∈ (complementVectorsOf i
        (EnlargedCertificates S X z y medium i)).attach,
      ∑ p ∈ splitPairDomain c, w ⟨c,p⟩) =
      ∑ a ∈ ConvenientCertificateCover.dyadicIndices X,
        ∑ c ∈ activeIndices S X z y medium i a.1 a.2.1 a.2.2,
          ∑ p ∈ boxedPairs c a.2.1 a.2.2, w ⟨c,p⟩ := by
  classical
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := complementPairs S X z y medium i)
    (t := ConvenientCertificateCover.dyadicIndices X)
    (g := dyadicLabel)
    (fun _ ht => label_mem ht) w
  have hsig : (∑ c ∈ (complementVectorsOf i
      (EnlargedCertificates S X z y medium i)).attach,
      ∑ p ∈ splitPairDomain c, w ⟨c,p⟩) =
      ∑ t ∈ complementPairs S X z y medium i, w t := by
    rw [complementPairs, Finset.sum_sigma]
  rw [hsig, ← hpartition]
  apply Finset.sum_congr rfl
  intro a _
  rw [label_fibre_eq_active_sigma a, Finset.sum_sigma]

end Erdos387Proof.ConvenientDyadicReduction
