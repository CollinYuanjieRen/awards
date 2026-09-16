import Erdos387Proof.ConvenientMainMass

/-! A reciprocal-mass bound for finite split-certificate families. The first
factor may equal one; only the final rough factor must exceed one. This is
the domain needed by the separated-error nonnegative enlargement. -/

set_option autoImplicit false
namespace Erdos387Proof.SplitCertificateMass
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open ConvenientMainMass ConvenientComplementGrouping MediumComplementGrouping
open MediumFactorWindow MediumComplementMass RoughHarmonic
open scoped BigOperators

theorem certificateTriple_mem {B K X z : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (t : SplitCertificate S X) (hB : 0<B)
    (hfactor : t.1.val.factor i=t.2.1*t.2.2)
    (hrough : ∀ j, IsZRough z (t.1.val.factor j))
    (hr : 0<t.2.1) (hs : 1<t.2.2)
    (hnear : X/2<B*t.1.val.value) (hX : t.1.val.value≤X) :
    ConvenientMainMass.certificateTriple i t∈ambientTriples B X z 1 X := by
  classical
  have hrrough : IsZRough z t.2.1 := by
    intro p hp hpz hpr
    apply hrough i p hp hpz
    rw [hfactor]
    exact hpr.trans (dvd_mul_right _ _)
  have hsrough : IsZRough z t.2.2 := by
    intro p hp hpz hps
    apply hrough i p hp hpz
    rw [hfactor]
    exact hps.trans (dvd_mul_left _ _)
  have hrsX : t.2.1*t.2.2≤X := hfactor ▸ t.1.val.factor_le i
  have hrX : t.2.1≤X := (Nat.le_mul_of_pos_right _ (by omega : 0<t.2.2)).trans hrsX
  have hsX : t.2.2≤X := (Nat.le_mul_of_pos_left _ hr).trans hrsX
  unfold ambientTriples
  rw [Finset.mem_sigma]
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro j
      exact mem_roughPositiveUpTo_iff.mpr
        ⟨t.1.val.positive j.val,t.1.val.factor_le j.val,hrough j.val⟩
    · exact mem_roughPositiveUpTo_iff.mpr ⟨hr,hrX,hrrough⟩
  · change t.2.2∈roughPositiveIoc z
      (lower B X ((∏ j,vector i t.1 j)*t.2.1) 1)
      (upper X ((∏ j,vector i t.1 j)*t.2.1) X)
    rw [prod_vector_eq_otherValue,mem_roughPositiveIoc]
    have hprod : t.2.2*(t.1.val.otherValue i*t.2.1)=t.1.val.value := by
      rw [← t.1.val.factor_mul_otherValue i,hfactor]
      ring
    have hD := Nat.mul_pos (t.1.val.otherValue_pos i) hr
    refine ⟨?_,le_min hsX ((Nat.le_div_iff_mul_le hD).mpr (hprod ▸ hX)),hsrough⟩
    apply max_lt_iff.mpr
    refine ⟨hs,?_⟩
    apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hB hD)).mpr
    calc
      X/2<B*t.1.val.value := hnear
      _=t.2.2*(B*(t.1.val.otherValue i*t.2.1)) := by rw [← hprod]; ring

/-- This generic finite statement has only pointwise arithmetic premises;
consumers must prove each from their actual certificate domain. -/
theorem sum_reciprocal_le {B K X z : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (F : Finset (SplitCertificate S X)) {C : ℝ} {N : ℕ}
    (hC : 0<C)
    (hcheb : ∀ t : ℕ, N≤t → (Nat.primeCounting t : ℝ)≤C*t/Real.log t)
    (hzN : N≤z) (hz : 2≤z) (hB : 0<B)
    (hdata : ∀ t∈F, t.1.val.factor i=t.2.1*t.2.2 ∧
      (∀ j, IsZRough z (t.1.val.factor j)) ∧ 0<t.2.1 ∧ 1<t.2.2 ∧
      X/2<B*t.1.val.value ∧ t.1.val.value≤X) :
    (∑ t∈F, (1 : ℝ)/t.1.val.value)≤
      (6*B*C/Real.log z)*roughReciprocalMass z X^(S.k+1) := by
  classical
  have hinj : Set.InjOn (ConvenientMainMass.certificateTriple i) (↑F : Set (SplitCertificate S X)) := by
    intro a ha b hb he
    apply groupingIndex_injOn_of_factor F (fun t ht => (hdata t ht).1) ha hb
    exact Prod.ext (congrArg (fun t => t.1.1) he)
      (Prod.ext (congrArg (fun t => t.1.2) he) (congrArg (fun t => t.2) he))
  have hsub : F.image (ConvenientMainMass.certificateTriple i)⊆ambientTriples B X z 1 X := by
    intro a ha
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hf,hr,hr0,hs,hnear,hupper⟩ := hdata t ht
    exact certificateTriple_mem i t hB hf hr hr0 hs hnear hupper
  calc
    _=∑ t∈F, tripleWeight (ConvenientMainMass.certificateTriple i t) :=
      Finset.sum_congr rfl (fun t ht => (certificateTriple_weight i t (hdata t ht).1).symm)
    _=∑ a∈F.image (ConvenientMainMass.certificateTriple i), tripleWeight a := (Finset.sum_image hinj).symm
    _≤∑ a∈ambientTriples B X z 1 X, tripleWeight a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by unfold tripleWeight; positivity)
    _≤_ := by
      have he : Fintype.card (ComplementIndex i)+2=S.k+1 := by
        simp only [ComplementIndex,Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin]
        have := S.hk3
        omega
      simpa only [he] using sum_ambientTriples_le (ι := ComplementIndex i)
        (X := X) (medium := X) hC hcheb hzN hz hB (by norm_num : 0<(1 : ℕ))

end Erdos387Proof.SplitCertificateMass
