import Erdos387Proof.MediumFactorWindow
import Erdos387Proof.ComplementTupleCounting

/-! Exact grouping by the full complementary vector. Distinct vectors with
identical products remain distinct; arbitrary signed summands are allowed. -/

namespace Erdos387Proof.MediumComplementGrouping

open Erdos387 MediumCertificateCover MediumFactorWindow
open scoped BigOperators

abbrev ComplementIndex {k : ℕ} (i : Fin k) := {j : Fin k // j ≠ i}

def vector {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (i : Fin S.k) (C : RefinedTupleCertificate S X) : ComplementIndex i → ℕ :=
  fun j => C.val.factor j.val

noncomputable def vectors {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (X z medium large : ℕ) (i : Fin S.k) : Finset (ComplementIndex i → ℕ) := by
  classical
  exact (certificates S X z medium large i).image (vector i)

noncomputable def representative {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    (c : {a // a ∈ vectors S X z medium large i}) : RefinedTupleCertificate S X :=
  Classical.choose (Finset.mem_image.mp c.property)

theorem representative_mem {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    (c : {a // a ∈ vectors S X z medium large i}) :
    representative c ∈ certificates S X z medium large i :=
  (Classical.choose_spec (Finset.mem_image.mp c.property)).1

theorem vector_representative {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    (c : {a // a ∈ vectors S X z medium large i}) :
    vector i (representative c) = c.val :=
  (Classical.choose_spec (Finset.mem_image.mp c.property)).2

theorem vector_eq_iff {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (i : Fin S.k) (C E : RefinedTupleCertificate S X) :
    vector i C = vector i E ↔ ∀ j, j ≠ i → C.val.factor j = E.val.factor j := by
  constructor
  · intro h j hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j.val j.property

/-- Exact partition into complementary fibres. -/
theorem sum_certificates_eq_sum_fibres {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k)
    (F : RefinedTupleCertificate S X → ℝ) :
    (∑ C ∈ certificates S X z medium large i, F C) =
      ∑ c ∈ (vectors S X z medium large i).attach,
        ∑ E ∈ fibre (representative c) i z medium large, F E := by
  classical
  have hf (c : {a // a ∈ vectors S X z medium large i}) :
      fibre (representative c) i z medium large =
        (certificates S X z medium large i).filter (fun E => vector i E = c.val) := by
    ext E
    simp only [fibre, Finset.mem_filter, ← vector_eq_iff,
      vector_representative]
  simp_rw [hf]
  rw [Finset.sum_attach (vectors S X z medium large i)
    (fun a => ∑ C ∈ (certificates S X z medium large i).filter
      (fun E => vector i E = a), F C)]
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro C hC
  exact Finset.mem_image.mpr ⟨C, hC, rfl⟩

/-- Signed sums over all medium certificates are exactly iterated sums over
independent complements and the one-dimensional coprime factor interval. -/
theorem sum_certificates_eq_sum_factors {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k) (hB : 0 < B)
    (F : RefinedTupleCertificate S X → ℝ) :
    (∑ C ∈ certificates S X z medium large i, F C) =
      ∑ c ∈ (vectors S X z medium large i).attach,
        ∑ d ∈ factors B X ((representative c).val.otherValue i)
            (CoverBPZ.refinementModulus S) medium large,
          F (fromFactor (representative c) i medium large d) := by
  classical
  rw [sum_certificates_eq_sum_fibres i F]
  apply Finset.sum_congr rfl
  intro c hc
  apply sum_fibre_eq_sum_factors _ _ hB
  exact (Finset.mem_filter.mp (representative_mem c)).2.2.2.2.2

end Erdos387Proof.MediumComplementGrouping
