import Erdos387Proof.MediumComplementGrouping

/-! Actual complementary-vector reciprocal mass and cardinality bounds.
Products are taken over exactly k-1 coordinates. -/

namespace Erdos387Proof.MediumComplementMass

open Erdos387 MediumCertificateCover MediumFactorWindow MediumComplementGrouping
open scoped BigOperators

theorem prod_vector_eq_otherValue {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) : (∏ j, vector i C j) = C.val.otherValue i := by
  classical
  exact (Finset.prod_subtype (Finset.univ.erase i)
    (fun j => by simp) C.val.factor).symm

theorem vector_coordinate_data {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {a : ComplementIndex i → ℕ} (ha : a ∈ vectors S X z medium large i)
    (j : ComplementIndex i) :
    0 < a j ∧ a j ≤ X ∧ IsZRough z (a j) := by
  classical
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp ha
  have hother := (Finset.mem_filter.mp hC).2.2.2.2.2
  exact ⟨C.val.positive j.val, C.val.factor_le j.val, (hother j.val j.property).2⟩

theorem sum_reciprocal_vectors_le {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k) :
    (∑ a ∈ vectors S X z medium large i, (1 : ℝ) / (∏ j, a j : ℕ)) ≤
      roughReciprocalMass z X ^ (S.k - 1) := by
  apply ComplementTupleCounting.sum_complement_rough_reciprocal_prod_le
  intro a ha j
  exact vector_coordinate_data ha j

/-- Representatives of distinct vectors are counted once even if their
products coincide. -/
theorem sum_reciprocal_representatives_le {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k) :
    (∑ c ∈ (vectors S X z medium large i).attach,
      (1 : ℝ) / (representative c).val.otherValue i) ≤
        roughReciprocalMass z X ^ (S.k - 1) := by
  have he (c : {a // a ∈ vectors S X z medium large i}) :
      (representative c).val.otherValue i = ∏ j, c.val j := by
    rw [← prod_vector_eq_otherValue, vector_representative]
  simp_rw [he]
  rw [Finset.sum_attach (vectors S X z medium large i)
    (fun a => (1 : ℝ) / (∏ j, a j : ℕ))]
  exact sum_reciprocal_vectors_le i

/-- The maximum complementary product is inherited from the original
product window, without requiring a new product-bound premise. -/
theorem vector_product_le_div {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} {i : Fin S.k}
    {a : ComplementIndex i → ℕ} (ha : a ∈ vectors S X z medium large i) :
    (∏ j, a j) ≤ X / (medium + 1) := by
  classical
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨_, hX, _, hmed, _, _⟩ := Finset.mem_filter.mp hC
  rw [prod_vector_eq_otherValue]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < medium + 1)).mpr
  calc
    C.val.otherValue i * (medium + 1) ≤ C.val.otherValue i * C.val.factor i :=
      Nat.mul_le_mul_left _ hmed
    _ = C.val.value := C.val.otherValue_mul_factor i
    _ ≤ X := hX

theorem card_vectors_le {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (i : Fin S.k) :
    ((vectors S X z medium large i).card : ℝ) ≤
      (X / (medium + 1) : ℕ) *
        (1 + Real.log (X / (medium + 1) : ℕ)) ^ (S.k - 1) := by
  apply ComplementTupleCounting.card_complement_tuples_le i
  · intro a ha j
    exact (vector_coordinate_data ha j).1
  · intro a ha
    exact vector_product_le_div ha

end Erdos387Proof.MediumComplementMass
