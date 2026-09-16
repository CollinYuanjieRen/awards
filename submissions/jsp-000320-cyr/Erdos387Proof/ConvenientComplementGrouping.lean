import Erdos387Proof.ConvenientCertificateCover
import Erdos387Proof.MediumComplementGrouping
import Erdos387Proof.TupleReplacement

/-!
# Exact complement and split-pair grouping for convenient certificates

The outer index records the full complementary vector together with the
ordered split pair `(r,s)`.  The refined certificate is recovered uniquely
from this data on the actual certificate domain, so it is not retained as a
separate moment index.  All product-window, roughness, squarefreeness and
medium constraints remain present through membership in the original
finite certificate set.
-/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientComplementGrouping

open Erdos387 ConvenientCertificateCover MediumComplementGrouping
open scoped BigOperators

abbrev GroupedIndex {k : ℕ} (i : Fin k) :=
  (ComplementIndex i → ℕ) × (ℕ × ℕ)

def groupingIndex {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (i : Fin S.k) (t : SplitCertificate S X) : GroupedIndex i :=
  (vector i t.1, t.2)

noncomputable def indicesOf {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k)
    (F : Finset (SplitCertificate S X)) : Finset (GroupedIndex i) := by
  classical
  exact F.image (groupingIndex i)

noncomputable def indices {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (X z y medium : ℕ) (i : Fin S.k) : Finset (GroupedIndex i) := by
  classical
  exact indicesOf i (certificates S X z y medium i)

theorem mem_indices_iff {B K X z y medium : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k} {a : GroupedIndex i} :
    a ∈ indices S X z y medium i ↔
      ∃ t ∈ certificates S X z y medium i, groupingIndex i t = a := by
  classical
  simp only [indices, indicesOf, Finset.mem_image]

/-- Purely algebraic injectivity for any finite family on which the chosen
coordinate is exactly the displayed ordered product.  This is reusable for
the original family and for later nonnegative enlargements. -/
theorem groupingIndex_injOn_of_factor {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    (F : Finset (SplitCertificate S X))
    (hfactor : ∀ t ∈ F, t.1.val.factor i = t.2.1 * t.2.2) :
    Set.InjOn (groupingIndex i) (↑F : Set (SplitCertificate S X)) := by
  classical
  intro t ht e he hindex
  have hp : t.2 = e.2 := by
    simpa only [groupingIndex] using
      congrArg (fun a : GroupedIndex i => a.2) hindex
  have hv : vector i t.1 = vector i e.1 := by
    simpa only [groupingIndex] using
      congrArg (fun a : GroupedIndex i => a.1) hindex
  have hi : t.1.val.factor i = e.1.val.factor i := by
    rw [hfactor t ht, hfactor e he, hp]
  have hC : t.1 = e.1 :=
    TupleReplacement.refined_eq_of_factor_and_complement_eq t.1 e.1 i hi
      ((vector_eq_iff i t.1 e.1).mp hv)
  exact Prod.ext hC hp

/-- On the actual domain, the complement and ordered split pair recover the
entire refined tuple and hence the whole split certificate. -/
theorem groupingIndex_injOn {B K X z y medium : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k} :
    Set.InjOn (groupingIndex i)
      (↑(certificates S X z y medium i) : Set (SplitCertificate S X)) := by
  classical
  apply groupingIndex_injOn_of_factor
  intro t ht
  exact (Finset.mem_filter.mp ht).2.2.2.1

noncomputable def representativeOf {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {F : Finset (SplitCertificate S X)}
    (a : {a // a ∈ indicesOf i F}) : SplitCertificate S X :=
  Classical.choose (Finset.mem_image.mp a.property)

theorem representativeOf_mem {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {F : Finset (SplitCertificate S X)} (a : {a // a ∈ indicesOf i F}) :
    representativeOf a ∈ F :=
  (Classical.choose_spec (Finset.mem_image.mp a.property)).1

theorem groupingIndex_representativeOf {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {F : Finset (SplitCertificate S X)} (a : {a // a ∈ indicesOf i F}) :
    groupingIndex i (representativeOf a) = a.val :=
  (Classical.choose_spec (Finset.mem_image.mp a.property)).2

noncomputable def representative {B K X z y medium : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    (a : {a // a ∈ indices S X z y medium i}) : SplitCertificate S X :=
  representativeOf a

theorem representative_mem {B K X z y medium : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    (a : {a // a ∈ indices S X z y medium i}) :
    representative a ∈ certificates S X z y medium i :=
  representativeOf_mem a

theorem groupingIndex_representative {B K X z y medium : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    (a : {a // a ∈ indices S X z y medium i}) :
    groupingIndex i (representative a) = a.val :=
  groupingIndex_representativeOf a

/-- Every chosen representative still satisfies the complete original
certificate mask. -/
theorem representative_constraints {B K X z y medium : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    (a : {a // a ∈ indices S X z y medium i}) :
    (representative a).1.val.value ≤ X ∧
      X / 2 < B * (representative a).1.val.value ∧
      (representative a).1.val.factor i =
        (representative a).2.1 * (representative a).2.2 ∧
      ∀ j, (representative a).1.val.factor j ≤ medium ∧
        Squarefree ((representative a).1.val.factor j) ∧
        IsZRough z ((representative a).1.val.factor j) := by
  classical
  exact (Finset.mem_filter.mp (representative_mem a)).2

noncomputable def complementVectorsOf {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k)
    (F : Finset (SplitCertificate S X)) :
    Finset (ComplementIndex i → ℕ) := by
  classical
  exact F.image (fun t => vector i t.1)

noncomputable def splitPairFibreOf {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k)
    (F : Finset (SplitCertificate S X)) (c : ComplementIndex i → ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (F.filter (fun t => vector i t.1 = c)).image Prod.snd

noncomputable def pairRepresentativeOf {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {F : Finset (SplitCertificate S X)}
    (c : {c // c ∈ complementVectorsOf i F})
    (p : {p // p ∈ splitPairFibreOf i F c.val}) : SplitCertificate S X :=
  Classical.choose (Finset.mem_image.mp p.property)

theorem pairRepresentativeOf_mem {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {F : Finset (SplitCertificate S X)}
    (c : {c // c ∈ complementVectorsOf i F})
    (p : {p // p ∈ splitPairFibreOf i F c.val}) :
    pairRepresentativeOf c p ∈ F :=
  (Finset.mem_filter.mp
    (Classical.choose_spec (Finset.mem_image.mp p.property)).1).1

theorem pairRepresentativeOf_vector {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {F : Finset (SplitCertificate S X)}
    (c : {c // c ∈ complementVectorsOf i F})
    (p : {p // p ∈ splitPairFibreOf i F c.val}) :
    vector i (pairRepresentativeOf c p).1 = c.val :=
  (Finset.mem_filter.mp
    (Classical.choose_spec (Finset.mem_image.mp p.property)).1).2

theorem pairRepresentativeOf_pair {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {F : Finset (SplitCertificate S X)}
    (c : {c // c ∈ complementVectorsOf i F})
    (p : {p // p ∈ splitPairFibreOf i F c.val}) :
    (pairRepresentativeOf c p).2 = p.val :=
  (Classical.choose_spec (Finset.mem_image.mp p.property)).2

/-- The finite split-pair fibre over a fixed full complementary vector. -/
noncomputable def splitPairFibre {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X z y medium : ℕ)
    (i : Fin S.k) (c : ComplementIndex i → ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact splitPairFibreOf i (certificates S X z y medium i) c

theorem mem_splitPairFibre_iff {B K X z y medium : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {c : ComplementIndex i → ℕ} {p : ℕ × ℕ} :
    p ∈ splitPairFibre S X z y medium i c ↔
      ∃ t ∈ certificates S X z y medium i,
        vector i t.1 = c ∧ t.2 = p := by
  classical
  simp only [splitPairFibre, splitPairFibreOf, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨t, ht, hc, rfl⟩
  · rintro ⟨t, ht, hc, hp⟩
    exact ⟨t, ⟨ht, hc⟩, hp⟩

/-- Generic exact regrouping for any explicit finite split family whose
selected factor is the displayed product. -/
theorem sum_family_eq_sum_indicesOf {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k)
    (Fset : Finset (SplitCertificate S X))
    (hfactor : ∀ t ∈ Fset, t.1.val.factor i = t.2.1 * t.2.2)
    (w : SplitCertificate S X → ℝ) :
    (∑ t ∈ Fset, w t) =
      ∑ a ∈ (indicesOf i Fset).attach, w (representativeOf a) := by
  classical
  apply Finset.sum_bij
      (fun t ht => ⟨groupingIndex i t,
        Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩)
  · intro t ht
    exact Finset.mem_attach _ _
  · intro t ht e he hte
    apply groupingIndex_injOn_of_factor Fset hfactor ht he
    exact congrArg Subtype.val hte
  · intro a ha
    refine ⟨representativeOf a, representativeOf_mem a, ?_⟩
    apply Subtype.ext
    exact groupingIndex_representativeOf a
  · intro t ht
    congr 1
    symm
    apply groupingIndex_injOn_of_factor Fset hfactor
      (representativeOf_mem
        ⟨groupingIndex i t, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩) ht
    exact groupingIndex_representativeOf
      ⟨groupingIndex i t, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩

/-- Exact two-level regrouping.  The moment-level outer index is only the
full complementary vector; the ordered split pair remains in its finite
inner fibre. -/
theorem sum_family_eq_sum_complements_splitPairs {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k)
    (Fset : Finset (SplitCertificate S X))
    (hfactor : ∀ t ∈ Fset, t.1.val.factor i = t.2.1 * t.2.2)
    (w : SplitCertificate S X → ℝ) :
    (∑ t ∈ Fset, w t) =
      ∑ c ∈ (complementVectorsOf i Fset).attach,
        ∑ p ∈ (splitPairFibreOf i Fset c.val).attach,
          w (pairRepresentativeOf c p) := by
  classical
  have hpartition :
      (∑ t ∈ Fset, w t) =
        ∑ c ∈ (complementVectorsOf i Fset).attach,
          ∑ t ∈ Fset.filter (fun t => vector i t.1 = c.val), w t := by
    rw [Finset.sum_attach (complementVectorsOf i Fset)
      (fun c => ∑ t ∈ Fset.filter (fun t => vector i t.1 = c), w t)]
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro t ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_bij
      (fun t ht => ⟨t.2, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩)
  · intro t ht
    exact Finset.mem_attach _ _
  · intro t ht e he hte
    have htF := (Finset.mem_filter.mp ht).1
    have heF := (Finset.mem_filter.mp he).1
    apply groupingIndex_injOn_of_factor Fset hfactor htF heF
    apply Prod.ext
    · exact (Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp he).2.symm
    · exact congrArg Subtype.val hte
  · intro p hp
    refine ⟨pairRepresentativeOf c p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨pairRepresentativeOf_mem c p, pairRepresentativeOf_vector c p⟩
    · apply Subtype.ext
      exact pairRepresentativeOf_pair c p
  · intro t ht
    congr 1
    have htF := (Finset.mem_filter.mp ht).1
    symm
    apply groupingIndex_injOn_of_factor Fset hfactor
      (pairRepresentativeOf_mem c
        ⟨t.2, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩) htF
    apply Prod.ext
    · exact (pairRepresentativeOf_vector c _).trans
        (Finset.mem_filter.mp ht).2.symm
    · exact pairRepresentativeOf_pair c _

/-- Exact regrouping for arbitrary weights.  The only outer index is the
complementary vector and ordered split pair. -/
theorem sum_certificates_eq_sum_indices {B K X z y medium : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k)
    (F : SplitCertificate S X → ℝ) :
    (∑ t ∈ certificates S X z y medium i, F t) =
      ∑ a ∈ (indices S X z y medium i).attach, F (representative a) := by
  classical
  simpa only [indices, representative] using
    sum_family_eq_sum_indicesOf i (certificates S X z y medium i)
      (fun t ht => (Finset.mem_filter.mp ht).2.2.2.1) F

/-- For the original convenient-certificate domain, the exact nested form
keeps the full complementary vector as the sole outer index and the ordered
split pair in its inner fibre.  In particular, the certificate itself never
becomes an additional outer moment index. -/
theorem sum_certificates_eq_sum_complements_splitPairs
    {B K X z y medium : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k)
    (F : SplitCertificate S X → ℝ) :
    (∑ t ∈ certificates S X z y medium i, F t) =
      ∑ c ∈ (complementVectorsOf i
          (certificates S X z y medium i)).attach,
        ∑ p ∈ (splitPairFibre S X z y medium i c.val).attach,
          F (pairRepresentativeOf c p) := by
  classical
  simpa only [splitPairFibre] using
    sum_family_eq_sum_complements_splitPairs i
      (certificates S X z y medium i)
      (fun t ht => (Finset.mem_filter.mp ht).2.2.2.1) F

end Erdos387Proof.ConvenientComplementGrouping
