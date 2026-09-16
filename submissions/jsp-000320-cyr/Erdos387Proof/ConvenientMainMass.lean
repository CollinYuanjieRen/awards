import Erdos387Proof.ConvenientComplementGrouping
import Erdos387Proof.ConvenientCertificateEnlargement
import Erdos387Proof.MediumComplementMass
import Erdos387Proof.MediumFactorGeometry
import ErdosProblems.Erdos387.LocalizedSwitchingEstimate

/-! The nonnegative convenient reciprocal mass is estimated before any
 dyadic partition. This avoids a logarithmic box-count loss in the zero mode. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientMainMass
open Erdos387 Erdos387.CoverBPZ RoughHarmonic MediumFactorWindow
open ConvenientComplementGrouping MediumComplementMass
open scoped BigOperators

theorem short_rough_mass_le {C : ℝ} {N B X z D y medium : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t → (Nat.primeCounting t : ℝ) ≤ C*t/Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B) (hD : 0 < D) (hy : 0 < y) :
    roughReciprocalIocMass z (lower B X D y) (upper X D medium) ≤
      (6*B*C/Real.log z)*roughReciprocalMass z X := by
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1<z by omega))
  have h := roughReciprocalIocMass_le_roughMass_div_log (A := lower B X D y) (U := upper X D medium)
    hC hcheb hzN hz (MediumFactorGeometry.lower_pos hy)
  have hratio := MediumFactorGeometry.upper_div_lower_le (X := X) (large := medium) hB hD hy
  have hmass := roughReciprocalMass_mono (z := z)
    ((Nat.div_le_self (upper X D medium) z).trans
      ((min_le_right medium (X/D)).trans (Nat.div_le_self X D)))
  apply h.trans
  apply mul_le_mul
  · apply div_le_div_of_nonneg_right _ hlog.le
    nlinarith
  · exact hmass
  · unfold roughReciprocalMass
    positivity
  · positivity

noncomputable def ambientTriples {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B X z y medium : ℕ) : Finset (Σ _cr : (ι → ℕ) × ℕ, ℕ) := by
  classical
  exact ((Fintype.piFinset (fun _ : ι => roughPositiveUpTo z X)).product
    (roughPositiveUpTo z X)).sigma fun cr =>
      roughPositiveIoc z (lower B X ((∏ j, cr.1 j)*cr.2) y)
        (upper X ((∏ j, cr.1 j)*cr.2) medium)

noncomputable def tripleWeight {ι : Type*} [Fintype ι]
    (t : Σ _cr : (ι → ℕ) × ℕ, ℕ) : ℝ :=
  1/(((∏ j, t.1.1 j)*t.1.2*t.2 : ℕ) : ℝ)

theorem sum_ambientTriples_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : ℝ} {N B X z y medium : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t → (Nat.primeCounting t : ℝ) ≤ C*t/Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B) (hy : 0 < y) :
    (∑ t ∈ ambientTriples (ι := ι) B X z y medium, tripleWeight t) ≤
      (6*B*C/Real.log z)*(roughReciprocalMass z X)^(Fintype.card ι+2) := by
  classical
  let R := roughPositiveUpTo z X
  let V := Fintype.piFinset (fun _ : ι => R)
  let Q : ℝ := (6*B*C/Real.log z)*roughReciprocalMass z X
  have hper : ∀ cr ∈ V.product R,
      (∑ s ∈ roughPositiveIoc z (lower B X ((∏ j, cr.1 j)*cr.2) y)
        (upper X ((∏ j, cr.1 j)*cr.2) medium), tripleWeight ⟨cr,s⟩) ≤
      (1/((∏ j, cr.1 j)*cr.2 : ℕ) : ℝ)*Q := by
    intro cr hcr
    obtain ⟨hc,hr⟩ := Finset.mem_product.mp hcr
    have hcpos : ∀ j, 0 < cr.1 j := fun j =>
      (mem_roughPositiveUpTo_iff.mp (Fintype.mem_piFinset.mp hc j)).1
    have hrpos := (mem_roughPositiveUpTo_iff.mp hr).1
    have he : (∑ s ∈ roughPositiveIoc z (lower B X ((∏ j, cr.1 j)*cr.2) y)
        (upper X ((∏ j, cr.1 j)*cr.2) medium), tripleWeight ⟨cr,s⟩) =
        (1/((∏ j, cr.1 j)*cr.2 : ℕ) : ℝ)*
          roughReciprocalIocMass z (lower B X ((∏ j, cr.1 j)*cr.2) y)
            (upper X ((∏ j, cr.1 j)*cr.2) medium) := by
      unfold roughReciprocalIocMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [tripleWeight, Nat.cast_mul, one_div, mul_inv]
    rw [he]
    exact mul_le_mul_of_nonneg_left
      (short_rough_mass_le hC hcheb hzN hz hB
        (Nat.mul_pos (Finset.prod_pos (fun j _ => hcpos j)) hrpos) hy) (by positivity)
  unfold ambientTriples
  rw [Finset.sum_sigma]
  calc
    _ ≤ ∑ cr ∈ V.product R, (1/((∏ j, cr.1 j)*cr.2 : ℕ) : ℝ)*Q :=
      Finset.sum_le_sum hper
    _ = Q*((∑ c ∈ V, (1 : ℝ)/(∏ j, c j : ℕ)) * ∑ r ∈ R, (1 : ℝ)/r) := by
      rw [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      push_cast
      simp only [one_div, mul_inv]
      ring
    _ = _ := by
      rw [ComplementTupleCounting.sum_piFinset_reciprocal_prod]
      change Q*(roughReciprocalMass z X^Fintype.card ι*roughReciprocalMass z X) = _
      dsimp [Q]
      rw [pow_add]
      ring

/-- The actual enlarged certificate is injected into a rough triple, with
all reciprocal weights preserved exactly. -/
def certificateTriple {B K X : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (t : ConvenientCertificateCover.SplitCertificate S X) :
    Σ _cr : (MediumComplementGrouping.ComplementIndex i → ℕ) × ℕ, ℕ :=
  ⟨(MediumComplementGrouping.vector i t.1,t.2.1),t.2.2⟩

theorem certificateTriple_weight {B K X : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (t : ConvenientCertificateCover.SplitCertificate S X)
    (ht : t.1.val.factor i=t.2.1*t.2.2) :
    tripleWeight (certificateTriple i t) = (1 : ℝ)/t.1.val.value := by
  unfold tripleWeight certificateTriple
  rw [prod_vector_eq_otherValue]
  have he : t.1.val.otherValue i*t.2.1*t.2.2=t.1.val.value := by
    rw [← t.1.val.factor_mul_otherValue i, ht]
    ring
  rw [he]

theorem certificateTriple_mem {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (hB : 0 < B)
    (t : ConvenientCertificateCover.SplitCertificate S X)
    (ht : t ∈ ConvenientCertificateEnlargement.certificates S X z y medium i) :
    certificateTriple i t ∈ ambientTriples B X z y medium := by
  classical
  obtain ⟨ht0,hX,hnear,hrs,hf⟩ := Finset.mem_filter.mp ht
  obtain ⟨hr,hs⟩ := Finset.mem_product.mp (Finset.mem_product.mp ht0).2
  have hr0 : 0<t.2.1 := (Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hr).1
  have hs0 : 0<t.2.2 := (Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hs).1
  have hrough : IsZRough z (t.2.1*t.2.2) := hrs ▸ (hf i).2.1
  have hrrough : IsZRough z t.2.1 := fun p hp hpz hpr =>
    hrough p hp hpz (hpr.trans (dvd_mul_right _ _))
  have hsrough : IsZRough z t.2.2 := fun p hp hpz hps =>
    hrough p hp hpz (hps.trans (dvd_mul_left _ _))
  unfold ambientTriples
  rw [Finset.mem_sigma]
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro j
      exact mem_roughPositiveUpTo_iff.mpr
        ⟨t.1.val.positive j.val,t.1.val.factor_le j.val,(hf j.val).2.1⟩
    · exact mem_roughPositiveUpTo_iff.mpr ⟨hr0,(Finset.mem_Ioc.mp hr).2,hrrough⟩
  · change t.2.2 ∈ roughPositiveIoc z
      (lower B X ((∏ j, MediumComplementGrouping.vector i t.1 j)*t.2.1) y)
      (upper X ((∏ j, MediumComplementGrouping.vector i t.1 j)*t.2.1) medium)
    rw [prod_vector_eq_otherValue, mem_roughPositiveIoc]
    have hprod : t.2.2*(t.1.val.otherValue i*t.2.1)=t.1.val.value := by
      rw [← t.1.val.factor_mul_otherValue i,hrs]
      ring
    have hD := Nat.mul_pos (t.1.val.otherValue_pos i) hr0
    have hsm : t.2.2 ≤ medium :=
      (Nat.le_mul_of_pos_left _ hr0).trans (hrs ▸ (hf i).1)
    refine ⟨?_,?_,hsrough⟩
    · apply max_lt_iff.mpr
      refine ⟨(Finset.mem_Ioc.mp hs).1, ?_⟩
      apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hB hD)).mpr
      calc
        X/2 < B*t.1.val.value := hnear
        _ = t.2.2*(B*(t.1.val.otherValue i*t.2.1)) := by rw [← hprod]; ring
    · exact le_min hsm ((Nat.le_div_iff_mul_le hD).mpr (hprod ▸ hX))



/-- The full original complement/split certificate count contributes only
k+1 cumulative rough factors and one inverse logarithm. -/
theorem sum_certificates_reciprocal_le {B K X z y medium : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) {C : ℝ} {N : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t → (Nat.primeCounting t : ℝ) ≤ C*t/Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B) (hy : 0 < y) :
    (∑ t ∈ ConvenientCertificateEnlargement.certificates S X z y medium i,
      (1 : ℝ)/t.1.val.value) ≤
      (6*B*C/Real.log z)*(roughReciprocalMass z X)^(S.k+1) := by
  classical
  let F := ConvenientCertificateEnlargement.certificates S X z y medium i
  have hinj : Set.InjOn (certificateTriple i) (↑F : Set (ConvenientCertificateCover.SplitCertificate S X)) := by
    intro a ha b hb he
    apply groupingIndex_injOn_of_factor F
      (fun t ht => ConvenientCertificateEnlargement.factor_eq ht) ha hb
    apply Prod.ext
    · exact congrArg (fun t => t.1.1) he
    · exact Prod.ext (congrArg (fun t => t.1.2) he) (congrArg (fun t => t.2) he)
  have hsub : F.image (certificateTriple i) ⊆ ambientTriples B X z y medium := by
    intro a ha
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
    exact certificateTriple_mem i hB t ht
  calc
    _ = ∑ t ∈ F, tripleWeight (certificateTriple i t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (certificateTriple_weight i t (ConvenientCertificateEnlargement.factor_eq ht)).symm
    _ = ∑ a ∈ F.image (certificateTriple i), tripleWeight a := (Finset.sum_image hinj).symm
    _ ≤ ∑ a ∈ ambientTriples B X z y medium, tripleWeight a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by unfold tripleWeight; positivity)
    _ ≤ _ := by
      have h := sum_ambientTriples_le (ι := MediumComplementGrouping.ComplementIndex i)
        (X := X) (medium := medium) hC hcheb hzN hz hB hy
      have he : Fintype.card (MediumComplementGrouping.ComplementIndex i)+2=S.k+1 := by
        simp only [MediumComplementGrouping.ComplementIndex,Fintype.card_subtype_compl,
          Fintype.card_subtype_eq,Fintype.card_fin]
        have := S.hk3
        omega
      simpa only [he] using h

end Erdos387Proof.ConvenientMainMass
