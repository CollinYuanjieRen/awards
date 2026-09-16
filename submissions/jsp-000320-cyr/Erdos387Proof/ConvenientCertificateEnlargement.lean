import Erdos387Proof.ConvenientCertificateCover

/-! Nonnegative enlargement before signed sieve expansion. Only the selected
coordinate's squarefreeness is dropped. All roughness, complementary
squarefreeness and original geometric masks remain explicit. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientCertificateEnlargement
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open scoped BigOperators

noncomputable def certificates {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium : ℕ) (i : Fin S.k) : Finset (SplitCertificate S X) := by
  classical
  exact (Finset.univ.product ((Finset.Ioc y X).product (Finset.Ioc y X))).filter fun t =>
    t.1.val.value ≤ X ∧ X/2 < B*t.1.val.value ∧ t.1.val.factor i = t.2.1*t.2.2 ∧
      ∀ j, t.1.val.factor j ≤ medium ∧ IsZRough z (t.1.val.factor j) ∧
        (j ≠ i → Squarefree (t.1.val.factor j))

theorem original_subset {B K X z y medium : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) : ConvenientCertificateCover.certificates S X z y medium i ⊆
      certificates S X z y medium i := by
  classical
  intro t ht
  obtain ⟨ht,hX,hnear,hrs,hf⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨ht,hX,hnear,hrs,fun j =>
    ⟨(hf j).1,(hf j).2.2,fun _ => (hf j).2.1⟩⟩

/-- The enlargement is justified for actual nonnegative class counts,
not for individual summands of a signed sieve polynomial. -/
theorem card_inter_le_sum_classes {B K X z y medium : ℕ}
    (S : BPZSection6Input B K) (hz : 2*S.k ≤ z) :
    (RefinedSquarefreeCandidates S X z ∩ RefinedConvenientErrors S X z y medium).card ≤
      ∑ i : Fin S.k, ∑ t ∈ certificates S X z y medium i,
        (MediumCertificateCover.siftedClass t.1 z).card := by
  classical
  apply (ConvenientCertificateCover.card_inter_le_sum_classes S hz).trans
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_le_sum_of_subset (original_subset S i)

theorem factor_eq {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium i) : t.1.val.factor i = t.2.1*t.2.2 := by
  classical
  exact (Finset.mem_filter.mp ht).2.2.2.1

theorem retained_data {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium i) :
    Squarefree (t.1.val.otherValue i) ∧ IsZRough z (t.1.val.otherValue i) ∧
      IsZRough z t.2.1 ∧ IsZRough z t.2.2 ∧
      t.2.1.Coprime (refinementModulus S*t.1.val.otherValue i) ∧
      t.2.2.Coprime (refinementModulus S*t.1.val.otherValue i) := by
  classical
  obtain ⟨_,_,_,hrs,hf⟩ := Finset.mem_filter.mp ht
  have hrough : IsZRough z (t.2.1*t.2.2) := hrs ▸ (hf i).2.1
  have hDsq : Squarefree (t.1.val.otherValue i) := by
    unfold TupleCertificate.otherValue
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro a _ b _ hab
      change IsRelPrime (t.1.val.factor a) (t.1.val.factor b)
      rw [← Nat.coprime_iff_isRelPrime]
      exact t.1.val.pairwise a b hab
    · intro j hj
      exact (hf j).2.2 (Finset.mem_erase.mp hj).1
  have hDrough : IsZRough z (t.1.val.otherValue i) := by
    intro p hp hpz hpd
    obtain ⟨j,_,hpj⟩ := (hp.prime.dvd_finsetProd_iff t.1.val.factor).mp hpd
    exact (hf j).2.1 p hp hpz hpj
  have hcopD : (t.2.1*t.2.2).Coprime (t.1.val.otherValue i) :=
    hrs ▸ t.1.val.factor_coprime_otherValue i
  have hcopM : (t.2.1*t.2.2).Coprime (refinementModulus S) := by
    apply Nat.Coprime.of_dvd_left (show t.2.1*t.2.2 ∣ t.1.val.value from by
      rw [← t.1.val.factor_mul_otherValue i,hrs]
      exact dvd_mul_right _ _)
    exact t.1.property.symm
  exact ⟨hDsq,hDrough,
    (fun p hp hpz hpr => hrough p hp hpz (hpr.trans (dvd_mul_right _ _))),
    (fun p hp hpz hps => hrough p hp hpz (hps.trans (dvd_mul_left _ _))),
    (Nat.Coprime.of_dvd_left (dvd_mul_right _ _) hcopM).mul_right
      (Nat.Coprime.of_dvd_left (dvd_mul_right _ _) hcopD),
    (Nat.Coprime.of_dvd_left (dvd_mul_left _ _) hcopM).mul_right
      (Nat.Coprime.of_dvd_left (dvd_mul_left _ _) hcopD)⟩


/-- Independent coordinate cutoffs remain available after removing the
selected squarefreeness condition. -/
theorem split_le_medium {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t ∈ certificates S X z y medium i) :
    t.2.1≤medium ∧ t.2.2≤medium := by
  classical
  obtain ⟨ht0,_,_,hrs,hf⟩ := Finset.mem_filter.mp ht
  obtain ⟨hr,hs⟩ := Finset.mem_product.mp (Finset.mem_product.mp ht0).2
  have hrpos : 0<t.2.1 := (Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hr).1
  have hspos : 0<t.2.2 := (Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hs).1
  have hprod : t.2.1*t.2.2≤medium := hrs ▸ (hf i).1
  exact ⟨(Nat.le_mul_of_pos_right _ hspos).trans hprod,
    (Nat.le_mul_of_pos_left _ hrpos).trans hprod⟩

end Erdos387Proof.ConvenientCertificateEnlargement
