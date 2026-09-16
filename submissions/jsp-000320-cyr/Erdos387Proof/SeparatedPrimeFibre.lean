import Erdos387Proof.SeparatedCertificateEnlargement
import Erdos387Proof.TupleReplacement

/-! Exact one-dimensional fibres of the anchored separated enlargement.
The selected small factor and full complement remain fixed. The inverse
phase unit mask includes the selected small factor, not just the complement.
-/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedPrimeFibre
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open MediumComplementGrouping ConvenientComplementGrouping
open SeparatedCertificateEnlargement
open scoped BigOperators

variable {B K X z y medium second gap : ℕ} {S : BPZSection6Input B K}
variable {i : Fin S.k}

noncomputable def fibre (a : SplitCertificate S X) : Finset (SplitCertificate S X) := by
  classical
  exact (certificates S X z y medium second gap i).filter (SameAnchorKey i · a)

noncomputable def primeFibre (a : SplitCertificate S X) : Finset ℕ :=
  (fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a).image
    (fun t =>  t.2.2)

/-- Every varying-coordinate condition is explicit; there is no arbitrary
coupled weight or forgotten tuple constraint. -/
noncomputable def domain (a : SplitCertificate S X) : Finset ℕ := by
  classical
  exact (Finset.Ioc 1 X).filter fun q => 
    Nat.log2 (q-1) = Nat.log2 (a.2.2-1) ∧ IsZRough y q ∧
    q.Coprime (refinementModulus S*a.1.val.otherValue i*a.2.1) ∧
    a.2.1*q  ≤  medium ∧ X/2  <  B*(a.1.val.otherValue i*a.2.1*q) ∧
    a.1.val.otherValue i*a.2.1*q  ≤  X

theorem otherValue_eq_of_key {a t : SplitCertificate S X}
    (h : SameAnchorKey i t a) : t.1.val.otherValue i = a.1.val.otherValue i :=
  otherValue_eq_of_factors_eq_off_index t.1.val a.1.val i
    ((vector_eq_iff i t.1 a.1).mp h.1)

theorem prime_injOn (a : SplitCertificate S X) :
    Set.InjOn (fun t : SplitCertificate S X =>  t.2.2)
      (↑(fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a) :
        Set (SplitCertificate S X)) := by
  classical
  intro t ht u hu hq
  obtain ⟨ht,htkey⟩ := Finset.mem_filter.mp ht
  obtain ⟨hu,hukey⟩ := Finset.mem_filter.mp hu
  apply SeparatedCertificateEnlargement.groupingIndex_injOn ht hu
  apply Prod.ext
  · exact htkey.1.trans hukey.1.symm
  · exact Prod.ext (htkey.2.1.trans hukey.2.1.symm) hq

theorem mem_primeFibre_iff (a : SplitCertificate S X)
    (ha : a ∈ certificates S X z y medium second gap i) (hzy : z  ≤  y) {q : ℕ} :
    q ∈ primeFibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a ↔
      q ∈ domain (y:=y) (medium:=medium) (i:=i) a := by
  classical
  constructor
  · intro hq
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ht,hkey⟩ := Finset.mem_filter.mp ht
    have hdata := admissible ht
    have hb := split_bounds ht
    have hD := otherValue_eq_of_key hkey
    have hr := hkey.2.1
    have hvalue : t.1.val.value = a.1.val.otherValue i*a.2.1*t.2.2 := by
      rw [← t.1.val.factor_mul_otherValue i,hdata.factor,hD,hr]
      ring
    have hret := ConvenientCertificateEnlargement.retained_data
      (mem_generic_split_enlargement ht)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hb.2.2.1,hb.2.2.2⟩,
      hkey.2.2,hdata.prime_rough,?_,?_,?_,?_⟩
    · simpa only [hD,hr] using hret.2.2.2.2.2.mul_right hdata.selected_coprime.symm
    · simpa only [hdata.factor,hr] using (hdata.factors i).1
    · simpa only [hvalue] using hdata.near
    · simpa only [hvalue] using hdata.upper
  · intro hq
    obtain ⟨hqI,hblock,hrough,hcop,hmedium,hnear,hupper⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1,hqX⟩ := Finset.mem_Ioc.mp hqI
    have hb := split_bounds ha
    have had := admissible ha
    have hret := ConvenientCertificateEnlargement.retained_data
      (mem_generic_split_enlargement ha)
    have hr0 : 0 < a.2.1 := by omega
    have hq0 : 0 < q := by omega
    have hD0 := a.1.val.otherValue_pos i
    have hrq0 := Nat.mul_pos hr0 hq0
    have hrqX : a.2.1*q  ≤  X := by
      apply (Nat.le_mul_of_pos_left (a.2.1*q) hD0).trans
      simpa only [Nat.mul_assoc] using hupper
    have hqMD := Nat.Coprime.of_dvd_right (dvd_mul_right _ _) hcop
    have hqr := Nat.Coprime.of_dvd_right (dvd_mul_left _ _) hcop
    have hprod := hret.2.2.2.2.1.mul_left hqMD
    let C := TupleReplacement.replaceRefined a.1 i (a.2.1*q) hrq0 hrqX hprod
    have hCi : C.val.factor i = a.2.1*q := by
      simp only [C,TupleReplacement.factor_replaceRefined,ite_true]
    have hCoff : ∀ j, j≠i → C.val.factor j=a.1.val.factor j := by
      intro j hji
      simp only [C,TupleReplacement.factor_replaceRefined,if_neg hji]
    have hvec : vector i C=vector i a.1 := (vector_eq_iff i C a.1).mpr hCoff
    have hval : C.val.value=a.1.val.otherValue i*a.2.1*q := by
      calc
        C.val.value=(a.2.1*q)*a.1.val.otherValue i :=
          TupleReplacement.value_replaceRefined a.1 i (a.2.1*q) hrq0 hrqX hprod
        _=a.1.val.otherValue i*a.2.1*q := by ring
    have hqroughz : IsZRough z q := fun p hp hpz =>  hrough p hp (hpz.trans_le hzy)
    have hprodrough : IsZRough z (a.2.1*q) := by
      intro p hp hpz hpd
      rcases hp.dvd_mul.mp hpd with hpr | hpq
      · exact hret.2.2.1 p hp hpz hpr
      · exact hqroughz p hp hpz hpq
    have hmem : (C,(a.2.1,q)) ∈ certificates S X z y medium second gap i := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hb.1,hb.2.1⟩,Finset.mem_Ioc.mpr ⟨hq1,hqX⟩⟩⟩,?_⟩
      refine { upper := by simpa only [hval] using hupper
               near := by simpa only [hval] using hnear
               factor := hCi
               small := had.small
               prime_rough := hrough
               selected_coprime := hqr.symm
               small_squarefree := had.small_squarefree
               factors := ?_
               anchor := ?_ }
      · intro j
        by_cases hji : j=i
        · subst j
          rw [hCi]
          exact ⟨hmedium,hprodrough,fun h =>  (h rfl).elim⟩
        · rw [hCoff j hji]
          exact had.factors j
      · obtain ⟨e,he,hkey⟩ := had.anchor
        exact ⟨e,he,hvec.trans hkey.1,hkey.2.1,hblock.trans hkey.2.2⟩
    apply Finset.mem_image.mpr
    exact ⟨(C,(a.2.1,q)),Finset.mem_filter.mpr ⟨hmem,hvec,rfl,hblock⟩,rfl⟩

theorem primeFibre_eq_domain (a : SplitCertificate S X)
    (ha : a ∈ certificates S X z y medium second gap i) (hzy : z  ≤  y) :
    primeFibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a =
      domain (y:=y) (medium:=medium) (i:=i) a := by
  ext q
  exact mem_primeFibre_iff a ha hzy

/-- Signed and complex summands are preserved exactly under the injective
varying-coordinate parameterization. -/
theorem sum_fibre_eq_domain {R : Type*} [AddCommMonoid R]
    (a : SplitCertificate S X)
    (ha : a ∈ certificates S X z y medium second gap i) (hzy : z  ≤  y) (w : ℕ → R) :
    (∑ t ∈ fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i) a,
      w t.2.2) = ∑ q ∈ domain (y:=y) (medium:=medium) (i:=i) a, w q := by
  classical
  rw [← primeFibre_eq_domain a ha hzy]
  exact (Finset.sum_image (fun t ht u hu h =>  prime_injOn a ht hu h)).symm

/-- The dyadic index of q-1 is exactly the open-left block convention. -/
theorem log2_sub_one_eq_iff {a q : ℕ} (_ha : 1 < a) :
    (1 < q ∧ Nat.log2 (q-1)=Nat.log2 (a-1)) ↔
      q ∈ Finset.Ioc (blockUpper a/2) (blockUpper a) := by
  have hhalf : blockUpper a/2=2^(Nat.log2 (a-1)) := by
    unfold blockUpper
    rw [pow_succ]
    omega
  have hpow : 0 < 2^(Nat.log2 (a-1)) := by positivity
  rw [Finset.mem_Ioc,hhalf]
  constructor
  · rintro ⟨hq,hlog⟩
    have hb := exact_prime_block q hq
    simpa only [hlog,blockUpper] using hb
  · intro hq
    have hq1 : 1 < q := by omega
    refine ⟨hq1,?_⟩
    apply (Nat.log2_eq_iff (by omega : q-1≠0)).mpr
    change 2^(Nat.log2 (a-1)) ≤ q-1 ∧ q-1 < 2^(Nat.log2 (a-1)+1)
    change 2^(Nat.log2 (a-1)) < q ∧ q ≤ 2^(Nat.log2 (a-1)+1) at hq
    omega

def lower (a : SplitCertificate S X) (i : Fin S.k) : ℕ :=
  (X/2)/(B*(a.1.val.otherValue i*a.2.1))

def upper (a : SplitCertificate S X) (i : Fin S.k) (medium : ℕ) : ℕ :=
  min (medium/a.2.1) (X/(a.1.val.otherValue i*a.2.1))

/-- The exact original product restrictions become one sharp interval;
there are no additional varying-coordinate conditions besides roughness
and the zero-extended reciprocal phase's unit mask. -/
theorem mem_domain_iff_sharp (a : SplitCertificate S X)
    (ha : a ∈ certificates S X z y medium second gap i) (hB : 0 < B) {q : ℕ} :
    q ∈ domain (y:=y) (medium:=medium) (i:=i) a ↔
      q ∈ Finset.Ioc (blockUpper a.2.2/2) (blockUpper a.2.2) ∧
      IsZRough y q ∧ q.Coprime (refinementModulus S*a.1.val.otherValue i*a.2.1) ∧
      lower a i < q ∧ q ≤ upper a i medium := by
  classical
  have hb := split_bounds ha
  have hr : 0 < a.2.1 := by omega
  have hD := a.1.val.otherValue_pos i
  have hDr := Nat.mul_pos hD hr
  have hm : q ≤ medium/a.2.1 ↔ a.2.1*q ≤ medium := by
    rw [Nat.le_div_iff_mul_le hr,mul_comm q]
  have hx : q ≤ X/(a.1.val.otherValue i*a.2.1) ↔
      a.1.val.otherValue i*a.2.1*q ≤ X := by
    rw [Nat.le_div_iff_mul_le hDr,mul_comm q]
  have hn : lower a i < q ↔ X/2 < B*(a.1.val.otherValue i*a.2.1*q) := by
    unfold lower
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hB hDr)]
    simp only [Nat.mul_comm,Nat.mul_left_comm]
  simp only [domain,Finset.mem_filter,Finset.mem_Ioc] at ⊢
  constructor
  · rintro ⟨⟨hq1,hqX⟩,hlog,hrough,hcop,hmed,hnear,hupper⟩
    refine ⟨Finset.mem_Ioc.mp ((log2_sub_one_eq_iff hb.2.2.1).mp ⟨hq1,hlog⟩),
      hrough,hcop,hn.mpr hnear,?_⟩
    exact le_min (hm.mpr hmed) (hx.mpr hupper)
  · rintro ⟨hblock,hrough,hcop,hnear,hupper⟩
    have hlog := (log2_sub_one_eq_iff hb.2.2.1).mpr (Finset.mem_Ioc.mpr hblock)
    have hux := (min_le_right _ _ : upper a i medium ≤ X/(a.1.val.otherValue i*a.2.1))
    exact ⟨⟨hlog.1,(hupper.trans hux).trans (Nat.div_le_self _ _)⟩,
      hlog.2,hrough,hcop,hm.mp (hupper.trans (min_le_left _ _)),hn.mp hnear,
      hx.mp (hupper.trans hux)⟩

/-- The finite outer key records the complete complementary vector, r,
and the q-1 dyadic block. It never counts source decompositions. -/
def key (i : Fin S.k) (a : SplitCertificate S X) : GroupedIndex i :=
  (vector i a.1,(a.2.1,Nat.log2 (a.2.2-1)))

theorem key_eq_iff (a t : SplitCertificate S X) :
    key i t=key i a ↔ SameAnchorKey i t a := by
  simp only [key,Prod.mk.injEq,SameAnchorKey]

noncomputable def keys (S : BPZSection6Input B K) (X z y medium second gap : ℕ)
    (i : Fin S.k) : Finset (GroupedIndex i) := by
  classical
  exact (certificates S X z y medium second gap i).image (key i)

noncomputable def representative
    (c : {c // c∈keys S X z y medium second gap i}) : SplitCertificate S X :=
  Classical.choose (Finset.mem_image.mp c.property)

theorem representative_mem (c : {c // c∈keys S X z y medium second gap i}) :
    representative c ∈ certificates S X z y medium second gap i :=
  (Classical.choose_spec (Finset.mem_image.mp c.property)).1

theorem key_representative (c : {c // c∈keys S X z y medium second gap i}) :
    key i (representative c)=c.val :=
  (Classical.choose_spec (Finset.mem_image.mp c.property)).2

/-- Exact grouping of the actual finite certificate sum, before taking
absolute values or applying any analytic bound. -/
theorem sum_certificates_eq_fibres {R : Type*} [AddCommMonoid R]
    (F : SplitCertificate S X → R) :
    (∑ a∈certificates S X z y medium second gap i,F a) =
      ∑ c∈(keys S X z y medium second gap i).attach,
        ∑ a∈fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap)
          (i:=i) (representative c),F a := by
  classical
  have hf (c : {c // c∈keys S X z y medium second gap i}) :
      fibre (z:=z) (y:=y) (medium:=medium) (second:=second) (gap:=gap) (i:=i)
          (representative c) =
        (certificates S X z y medium second gap i).filter (fun a =>  key i a=c.val) := by
    ext a
    simp only [fibre,Finset.mem_filter,← key_eq_iff,key_representative]
  simp_rw [hf]
  rw [Finset.sum_attach (keys S X z y medium second gap i)
    (fun c =>  ∑ a∈(certificates S X z y medium second gap i).filter
      (fun a =>  key i a=c),F a)]
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro a ha
  exact Finset.mem_image.mpr ⟨a,ha,rfl⟩

/-- A single original anchor supplies the analytic certificate for this
whole fibre, including the near-product inequality needed by the tent weight. -/
theorem exists_anchor_phase_data_near {g : ℕ} (a : SplitCertificate S X)
    (ha : a∈certificates S X z y medium second gap i)
    (hz : 2*S.k ≤ z) (hsecond : 1 ≤  second) (hg : Squarefree g)
    (hsupport : ∀ p∈g.primeFactors,p < z) :
    ∃ (n : ℕ) (C : SeparatedCertificatePhase.CertificatePhaseData S n y medium second gap g),
      C.i₀=i ∧ C.q C.i₀ ≤ blockUpper a.2.2 ∧
      (∀ j, j≠i → C.E.factor j=a.1.val.factor j) ∧
      C.modulus=g*a.2.1*a.1.val.otherValue i*refinementModulus S ∧
      X/2 < B*C.E.value := by
  obtain ⟨C,hi,hq,hf,hmod⟩ := SeparatedCertificateCover.exists_source_phase_data
    (anchor_mem ha) hz hsecond hg hsupport
  have hvalue : C.E.value=(anchor ha).1.val.value := by
    unfold CoverDivisorTuple.value TupleCertificate.value
    apply Finset.prod_congr rfl
    intro j hj
    exact hf j
  refine ⟨_,C,hi,?_,?_,?_,?_⟩
  · rw [hi,hq]
    have hp := (SeparatedCertificateCover.selected_prime hsecond (anchor_mem ha)).1.one_lt
    have hb := (exact_prime_block (anchor ha).2.2 hp).2
    simpa only [blockUpper,← (anchor_key ha).2.2] using hb
  · intro j hji
    rw [hf j]
    exact ((vector_eq_iff i a.1 (anchor ha).1).mp (anchor_key ha).1 j hji).symm
  · rw [hmod,anchor_complement_eq ha,← (anchor_key ha).2.1]
  · rw [hvalue]
    exact (SeparatedCertificateCover.geometry (anchor_mem ha)).2.1

end Erdos387Proof.SeparatedPrimeFibre
