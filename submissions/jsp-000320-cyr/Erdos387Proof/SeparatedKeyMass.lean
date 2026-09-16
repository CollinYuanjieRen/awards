import Erdos387Proof.SeparatedPrimeFibre
import Erdos387Proof.ComplementTupleCounting
import Erdos387Proof.MediumComplementMass

/-! Nonnegative reciprocal counting of the actual separated outer keys.
Each complementary vector, retained small factor, and dyadic block is
counted once; source decomposition witnesses are never summation indices. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedKeyMass
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open MediumComplementGrouping ConvenientComplementGrouping
open MediumComplementMass
open SeparatedCertificateEnlargement SeparatedPrimeFibre
open scoped BigOperators

noncomputable def keyWeight {B K : ℕ} {S : BPZSection6Input B K} {i : Fin S.k}
    (c : GroupedIndex i) : ℝ := 1/((∏ j,c.1 j)*c.2.1 : ℕ)

theorem keys_subset_box {B K X z y medium second gap : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) :
    keys S X z y medium second gap i ⊆
      (Fintype.piFinset (fun _ : ComplementIndex i => roughPositiveUpTo z X)).product
        ((roughPositiveUpTo z X).product (Finset.range (Nat.log2 X+1))) := by
  classical
  intro c hc
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
  have hd := admissible ha
  have hb := split_bounds ha
  have hr := ConvenientCertificateEnlargement.retained_data (mem_generic_split_enlargement ha)
  apply Finset.mem_product.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro j
    exact mem_roughPositiveUpTo_iff.mpr
      ⟨a.1.val.positive j.val,a.1.val.factor_le j.val,(hd.factors j.val).2.1⟩
  · apply Finset.mem_product.mpr
    constructor
    · exact mem_roughPositiveUpTo_iff.mpr ⟨hb.1,hb.2.1,hr.2.2.1⟩
    · apply Finset.mem_range.mpr
      change Nat.log2 (a.2.2-1)<Nat.log2 X+1
      have hle : a.2.2-1≤X := by omega
      apply Nat.lt_succ_of_le
      simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b:=2) hle)

theorem sum_keys_weight_le {B K X z y medium second gap : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) :
    (∑ c∈keys S X z y medium second gap i,keyWeight c)≤
      (Nat.log2 X+1 : ℕ)*roughReciprocalMass z X^S.k := by
  classical
  let R := roughPositiveUpTo z X
  let V := Fintype.piFinset (fun _ : ComplementIndex i => R)
  let J := Finset.range (Nat.log2 X+1)
  calc
    _ ≤ ∑ c∈V.product (R.product J),keyWeight c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (keys_subset_box S i)
      intro c hc hn
      unfold keyWeight
      positivity
    _ = (Nat.log2 X+1 : ℕ)*
        ((∑ c∈V,(1 : ℝ)/(∏ j,c j : ℕ))*(∑ r∈R,(1 : ℝ)/r)) := by
      simp only [Finset.product_eq_sprod,Finset.sum_product,keyWeight]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,J]
      rw [Finset.sum_mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      push_cast
      simp only [one_div,mul_inv]
    _ = _ := by
      rw [ComplementTupleCounting.sum_piFinset_reciprocal_prod]
      have hk : 1≤S.k := by have := S.hk3; omega
      simp only [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin]
      change (Nat.log2 X+1 : ℕ)*(roughReciprocalMass z X^(S.k-1)*roughReciprocalMass z X)=_
      rw [← pow_succ,Nat.sub_add_cancel hk]

theorem blockUpper_mul_retained_le {B K X z y medium second gap : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {a : SplitCertificate S X}
    (ha : a∈certificates S X z y medium second gap i) :
    blockUpper a.2.2*(a.1.val.otherValue i*a.2.1)≤2*X := by
  have hd := admissible ha
  have hb := split_bounds ha
  have hv : (a.1.val.otherValue i*a.2.1)*a.2.2=a.1.val.value := by
    rw [← a.1.val.factor_mul_otherValue i,hd.factor]
    ring
  calc
    _ ≤ (2*a.2.2)*(a.1.val.otherValue i*a.2.1) :=
      Nat.mul_le_mul_right _ (blockUpper_le_twice hb.2.2.1 le_rfl)
    _ = 2*a.1.val.value := by rw [← hv]; ring
    _ ≤ _ := Nat.mul_le_mul_left 2 hd.upper

theorem blockUpper_le_weight {B K X z y medium second gap : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {a : SplitCertificate S X}
    (ha : a∈certificates S X z y medium second gap i) :
    (blockUpper a.2.2 : ℝ)≤2*X*keyWeight (key i a) := by
  have hb := split_bounds ha
  have hD : (0 : ℝ)<(a.1.val.otherValue i*a.2.1 : ℕ) := by
    exact_mod_cast Nat.mul_pos (a.1.val.otherValue_pos i) (by omega : 0<a.2.1)
  unfold keyWeight key
  rw [prod_vector_eq_otherValue,mul_one_div]
  apply (le_div_iff₀ hD).mpr
  exact_mod_cast blockUpper_mul_retained_le ha

end Erdos387Proof.SeparatedKeyMass
