import Erdos387Proof.ConvenientMomentApplicability
import Erdos387Proof.ConvenientSplitFibre
import Erdos387Proof.SquarefreeTupleMultiplicity
import Erdos387Proof.MediumComplementMass

/-! Actual complement-only dyadic moment domains. Individual boxes retain
roughness and units. Sharp product constraints select active complements and
are subsequently separated exactly; they never enter an arbitrary weight. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientMomentBoxes
open Erdos387 Erdos387.CoverBPZ
open ConvenientCertificateCover ConvenientComplementGrouping ConvenientSplitFibre
open MediumComplementGrouping MediumComplementMass ConvenientMomentApplicability
open scoped BigOperators

noncomputable abbrev Index {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium : ℕ) (i : Fin S.k) :=
  {c // c ∈ complementVectorsOf i (ConvenientSplitFibre.EnlargedCertificates S X z y medium i)}

def product {B K X z y medium : ℕ} {S : BPZSection6Input B K} {i : Fin S.k}
    (c : Index S X z y medium i) : ℕ := ∏ j, c.val j

theorem product_eq_otherValue {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} (c : Index S X z y medium i) :
    product c=(complementRepresentative c).1.val.otherValue i := by
  unfold product
  rw [← vector_complementRepresentative c]
  exact prod_vector_eq_otherValue _ _

theorem product_data {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (c : Index S X z y medium i) :
    0 < product c ∧ product c ≤ X ∧ Squarefree (product c) ∧ IsZRough z (product c) := by
  classical
  rw [product_eq_otherValue]
  have hc := complementRepresentative_mem c
  have hX := (Finset.mem_filter.mp hc).2.1
  have hDle : (complementRepresentative c).1.val.otherValue i ≤
      (complementRepresentative c).1.val.value :=
    Nat.le_of_dvd (complementRepresentative c).1.val.value_pos (by
      rw [← (complementRepresentative c).1.val.factor_mul_otherValue i]
      exact dvd_mul_left _ _)
  have hd := ConvenientCertificateEnlargement.retained_data hc
  exact ⟨(complementRepresentative c).1.val.otherValue_pos i,hDle.trans hX,hd.1,hd.2.1⟩

theorem coordinate_pos {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (c : Index S X z y medium i) (j : ComplementIndex i) : 0 < c.val j := by
  rw [← vector_complementRepresentative c]
  exact (complementRepresentative c).1.val.positive j.val

theorem coordinates_coprime {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (c : Index S X z y medium i) (a b : ComplementIndex i) (hab : a≠b) :
    (c.val a).Coprime (c.val b) := by
  rw [← vector_complementRepresentative c]
  exact (complementRepresentative c).1.val.pairwise a.val b.val
    (fun h => hab (Subtype.ext h))

/-- Membership records existence of an original masked pair only at the
complement level. It does not put a pair-dependent mask in a moment weight. -/
noncomputable def activeIndices {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium : ℕ) (i : Fin S.k) (e r s : ℕ) : Finset (Index S X z y medium i) := by
  classical
  exact (complementVectorsOf i (ConvenientSplitFibre.EnlargedCertificates S X z y medium i)).attach.filter
    fun c => product c ∈ Finset.Ico (2^e) (2^(e+1)) ∧
      ∃ p ∈ splitPairDomain c,
        p.1 ∈ Finset.Ico (2^r) (2^(r+1)) ∧ p.2 ∈ Finset.Ico (2^s) (2^(s+1))

theorem product_mem_interval {B K X z y medium e r s : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {c : Index S X z y medium i}
    (hc : c ∈ activeIndices S X z y medium i e r s) :
    product c ∈ Finset.Ico (2^e) (2^(e+1)) := by
  classical
  exact (Finset.mem_filter.mp hc).2.1

theorem active_scale_product_le_X {B K X z y medium e r s : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (hne : (activeIndices S X z y medium i e r s).Nonempty) :
    2^e*2^r*2^s ≤ X := by
  classical
  obtain ⟨c,hc⟩ := hne
  obtain ⟨hD,p,hp,hr,hs⟩ := (Finset.mem_filter.mp hc).2
  have hupper := (mem_splitPairDomain_iff c).mp hp |>.2.2.2.2.2.2.2.2
  rw [← product_eq_otherValue] at hupper
  exact (Nat.mul_le_mul (Nat.mul_le_mul (Finset.mem_Ico.mp hD).1
    (Finset.mem_Ico.mp hr).1) (Finset.mem_Ico.mp hs).1).trans hupper

/-- Each independent variable retains all arithmetic filters and may be
cut at a complement-dependent prefix endpoint for finite Abel summation. -/
noncomputable def variableBox {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g b cut : ℕ) (c : Index S X z y medium i) : Finset ℕ := by
  classical
  exact (Finset.Ico (2^b) (2^(b+1))).filter fun n =>
    y < n ∧ n ≤ medium ∧ n ≤ cut ∧ IsZRough z n ∧
      n.Coprime (momentModulus (refinementModulus S) g (product c))

noncomputable def ambientBox (z y medium b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (2^b) (2^(b+1))).filter fun n =>
    y < n ∧ n ≤ medium ∧ IsZRough z n

def upperEndpoint (medium b : ℕ) : ℕ := min medium (2^(b+1)-1)

theorem variableBox_subset_ambient {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (g b cut : ℕ) (c : Index S X z y medium i) :
    variableBox g b cut c ⊆ ambientBox z y medium b := by
  classical
  intro n hn
  obtain ⟨hn,hy,hm,_,hr,_⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hn,hy,hm,hr⟩

theorem ambientBox_data {z y medium b n : ℕ} (hn : n ∈ ambientBox z y medium b) :
    0 < n ∧ n ≤ upperEndpoint medium b ∧ IsZRough z n := by
  classical
  obtain ⟨hn,hy,hm,hr⟩ := Finset.mem_filter.mp hn
  refine ⟨(Nat.zero_le y).trans_lt hy,le_min hm ?_,hr⟩
  have := (Finset.mem_Ico.mp hn).2
  omega

theorem variableBox_unit {B K X z y medium n : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {g b cut : ℕ}
    {c : Index S X z y medium i} (hn : n ∈ variableBox g b cut c) :
    n.Coprime (momentModulus (refinementModulus S) g (product c)) := by
  classical
  exact (Finset.mem_filter.mp hn).2.2.2.2.2

theorem card_variableBox_le {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (g b cut : ℕ) (c : Index S X z y medium i) :
    (variableBox g b cut c).card ≤ 2^b := by
  classical
  have h := Finset.card_filter_le (Finset.Ico (2^b) (2^(b+1)))
    (fun n => y < n ∧ n ≤ medium ∧ n ≤ cut ∧ IsZRough z n ∧
      n.Coprime (momentModulus (refinementModulus S) g (product c)))
  have he : (Finset.Ico (2^b) (2^(b+1))).card=2^b := by
    rw [Nat.card_Ico,pow_succ]
    omega
  simpa only [variableBox,he] using h

theorem card_ambientBox_le (z y medium b : ℕ) : (ambientBox z y medium b).card ≤ 2^b := by
  classical
  have h := Finset.card_filter_le (Finset.Ico (2^b) (2^(b+1)))
    (fun n => y < n ∧ n ≤ medium ∧ IsZRough z n)
  have he : (Finset.Ico (2^b) (2^(b+1))).card=2^b := by
    rw [Nat.card_Ico,pow_succ]
    omega
  simpa only [ambientBox,he] using h

theorem card_product_image_le {B K X z y medium e r s : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} :
    ((activeIndices S X z y medium i e r s).image product).card ≤ 2^e := by
  classical
  have hsub : (activeIndices S X z y medium i e r s).image product ⊆
      Finset.Ico (2^e) (2^(e+1)) := by
    intro d hd
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hd
    exact product_mem_interval hc
  have h := Finset.card_le_card hsub
  have he : (Finset.Ico (2^e) (2^(e+1))).card=2^e := by
    rw [Nat.card_Ico,pow_succ]
    omega
  exact h.trans_eq he

/-- Multiplicity is charged only for complementary vectors with the same
product, never for their split pairs or separating Fourier frequencies. -/
theorem fibre_card_le {B K N : ℕ} {S : BPZSection6Input B K} (i : Fin S.k)
    (I : Finset (Index S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i))
    (hN : 0 < N) {d : ℕ} (hd : d ∈ I.image product) :
    (I.filter fun c => product c=d).card ≤ S.k^(N^2) := by
  classical
  obtain ⟨c,hc,hcd⟩ := Finset.mem_image.mp hd
  have hddata := product_data c
  rw [hcd] at hddata
  let F := I.filter fun c => product c=d
  let A := F.image (fun c => c.val)
  have hcard : A.card=F.card := Finset.card_image_of_injective _ Subtype.val_injective
  rw [← hcard]
  apply SquarefreeTupleMultiplicity.card_complement_tuples_le_k_pow_square hN
    (by have := S.hk3; omega) i A hddata.2.2.1 hddata.2.2.2 hddata.2.1
  · intro f hf j
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hf
    exact coordinate_pos c j
  · intro f hf a b hab
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hf
    exact coordinates_coprime c a b hab
  · intro f hf
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hf
    exact (Finset.mem_filter.mp hc).2

theorem card_activeIndices_le {B K N e r s : ℕ} {S : BPZSection6Input B K}
    (i : Fin S.k) (hN : 0 < N) :
    (activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
      (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s).card ≤
      S.k^(N^2)*2^e := by
  classical
  let I := activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
    (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s
  have h := IndexedConvenientMoment.sum_comp_le_maxFiber_mul_sum_image I product
    (fun _ => 1) (S.k^(N^2)) (fun d hd => fibre_card_le i I hN hd)
  have hcard : I.card ≤ S.k^(N^2)*(I.image product).card := by simpa using h
  exact hcard.trans (Nat.mul_le_mul_left _ card_product_image_le)

/-- The precise tuple, root and frequency moduli remain available on all
positive complementary products, with a harmless value at zero. -/
noncomputable def modulus {B K : ℕ} (S : BPZSection6Input B K) (g D : ℕ) : ℕ :=
  momentModulus (refinementModulus S) g D

instance modulus_neZero {B K : ℕ} (S : BPZSection6Input B K) (g D : ℕ) [NeZero g] :
    NeZero (modulus S g D) := by
  have : NeZero (refinementModulus S) := ⟨(refinementModulus_pos S).ne'⟩
  exact momentModulus_neZero _ _ _

theorem sum_box_card_le {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (I : Finset (Index S X z y medium i)) (g b : ℕ)
    (cut : Index S X z y medium i → ℕ) :
    (∑ c ∈ I, (variableBox g b (cut c) c).card) ≤ I.card*2^b := by
  calc
    _ ≤ ∑ _c ∈ I, 2^b := Finset.sum_le_sum (fun c _ => card_variableBox_le g b (cut c) c)
    _ = _ := by simp

theorem sum_modulus_mul_card_le {B K X z y medium e r s : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} (g : ℕ)
    (cut : Index S X z y medium i → ℕ) :
    let I := activeIndices S X z y medium i e r s
    (∑ c ∈ I, modulus S g (product c)*(variableBox g r (cut c) c).card) ≤
      2*refinementModulus S*g*I.card*2^e*2^r := by
  classical
  dsimp only
  calc
    _ ≤ ∑ _c ∈ activeIndices S X z y medium i e r s,
        (refinementModulus S*(2*2^e)*g)*2^r := by
      apply Finset.sum_le_sum
      intro c hc
      have hD : product c ≤ 2*2^e := by
        simpa only [pow_succ,mul_comm] using (Finset.mem_Ico.mp (product_mem_interval hc)).2.le
      rw [modulus,momentModulus_eq (product_data c).1]
      exact Nat.mul_le_mul (Nat.mul_le_mul_right g (Nat.mul_le_mul_left _ hD))
        (card_variableBox_le g r (cut c) c)
    _ = _ := by simp [mul_comm,mul_left_comm,mul_assoc]

end Erdos387Proof.ConvenientMomentBoxes
