import Erdos387Proof.TupleReplacement

/-! The exact one-dimensional factor interval in a fixed complement fibre. -/

namespace Erdos387Proof.MediumFactorWindow

open Erdos387 Erdos387Proof.TupleReplacement
open scoped BigOperators

def lower (B X D medium : ℕ) : ℕ := max medium ((X / 2) / (B * D))
def upper (X D large : ℕ) : ℕ := min large (X / D)

noncomputable def factors (B X D M medium large : ℕ) : Finset ℕ :=
  (Finset.Ioc (lower B X D medium) (upper X D large)).filter
    (fun d => Nat.Coprime d (M * D))

theorem mem_factors_iff {B X D M medium large d : ℕ} (hB : 0 < B) (hD : 0 < D) :
    d ∈ factors B X D M medium large ↔
      d * D ≤ X ∧ X / 2 < B * (d * D) ∧ medium < d ∧ d ≤ large ∧
        Nat.Coprime d (M * D) := by
  have hnear : (X / 2) / (B * D) < d ↔ X / 2 < B * (d * D) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hB hD)]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have hprod : d ≤ X / D ↔ d * D ≤ X := Nat.le_div_iff_mul_le hD
  simp only [factors, Finset.mem_filter, Finset.mem_Ioc, lower, upper,
    max_lt_iff, le_min_iff, hnear, hprod]
  tauto

theorem factor_pos_of_mem {B X D M medium large d : ℕ}
    (hd : d ∈ factors B X D M medium large) : 0 < d := by
  have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
  unfold lower at h
  omega

theorem factor_le_X_of_mem {B X D M medium large d : ℕ}
    (hd : d ∈ factors B X D M medium large) : d ≤ X := by
  have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).2
  exact (le_trans h (min_le_right _ _)).trans (Nat.div_le_self X D)

noncomputable def fibre {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (z medium large : ℕ) :
    Finset (RefinedTupleCertificate S X) := by
  classical
  exact (MediumCertificateCover.certificates S X z medium large i).filter
    (fun E => ∀ j, j ≠ i → E.val.factor j = C.val.factor j)

theorem factor_mem_of_mem_fibre {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    (C E : RefinedTupleCertificate S X) (i : Fin S.k) (hB : 0 < B)
    (hE : E ∈ fibre C i z medium large) :
    E.val.factor i ∈ factors B X (C.val.otherValue i)
      (CoverBPZ.refinementModulus S) medium large := by
  classical
  obtain ⟨hcert, hother⟩ := Finset.mem_filter.mp hE
  have hD := otherValue_eq_of_factors_eq_off_index E.val C.val i hother
  have hvalue : E.val.value = E.val.factor i * C.val.otherValue i := by
    rw [← E.val.factor_mul_otherValue i, hD]
  obtain ⟨_, hvX, hnear, hm, hl, hrest⟩ := Finset.mem_filter.mp hcert
  rw [hvalue] at hvX hnear
  apply (mem_factors_iff hB (C.val.otherValue_pos i)).mpr
  refine ⟨hvX, hnear, hm, hl, ?_⟩
  apply Nat.Coprime.mul_right
  · exact (E.property.of_dvd_right (by
      rw [← E.val.factor_mul_otherValue i]
      exact dvd_mul_right _ _)).symm
  · rw [← hD]
    exact E.val.factor_coprime_otherValue i

noncomputable def fromFactor {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (medium large d : ℕ) :
    RefinedTupleCertificate S X := by
  classical
  exact if hd : d ∈ factors B X (C.val.otherValue i)
      (CoverBPZ.refinementModulus S) medium large then
    replaceRefined C i d (factor_pos_of_mem hd) (factor_le_X_of_mem hd)
      (Finset.mem_filter.mp hd).2
  else C

theorem fromFactor_mem_fibre {B K X z medium large d : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (hB : 0 < B)
    (hother : ∀ j, j ≠ i → Squarefree (C.val.factor j) ∧ IsZRough z (C.val.factor j))
    (hd : d ∈ factors B X (C.val.otherValue i)
      (CoverBPZ.refinementModulus S) medium large) :
    fromFactor C i medium large d ∈ fibre C i z medium large := by
  classical
  unfold fromFactor
  rw [dif_pos hd]
  apply Finset.mem_filter.mpr
  constructor
  · rw [replaceRefined_mem_certificates_iff C i d _ _ _ hother]
    obtain ⟨h1, h2, h3, h4, _⟩ := (mem_factors_iff hB (C.val.otherValue_pos i)).mp hd
    exact ⟨h1, h2, h3, h4⟩
  · intro j hji
    simp only [factor_replaceRefined, if_neg hji]

theorem fromFactor_factor {B K X medium large d : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k)
    (hd : d ∈ factors B X (C.val.otherValue i)
      (CoverBPZ.refinementModulus S) medium large) :
    (fromFactor C i medium large d).val.factor i = d := by
  classical
  simp only [fromFactor, dif_pos hd, factor_replaceRefined, ite_true]

/-- Exact regrouping within one complementary fibre, valid for arbitrary
signed real weights. -/
theorem sum_fibre_eq_sum_factors {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (hB : 0 < B)
    (hother : ∀ j, j ≠ i → Squarefree (C.val.factor j) ∧ IsZRough z (C.val.factor j))
    (F : RefinedTupleCertificate S X → ℝ) :
    (∑ E ∈ fibre C i z medium large, F E) =
      ∑ d ∈ factors B X (C.val.otherValue i)
          (CoverBPZ.refinementModulus S) medium large,
        F (fromFactor C i medium large d) := by
  classical
  apply Finset.sum_bij (fun E _ => E.val.factor i)
  · intro E hE
    exact factor_mem_of_mem_fibre C E i hB hE
  · intro E hE G hG heq
    apply refined_eq_of_factor_and_complement_eq E G i heq
    intro j hji
    exact ((Finset.mem_filter.mp hE).2 j hji).trans
      ((Finset.mem_filter.mp hG).2 j hji).symm
  · intro d hd
    exact ⟨fromFactor C i medium large d,
      fromFactor_mem_fibre C i hB hother hd, fromFactor_factor C i hd⟩
  · intro E hE
    congr 1
    have hd := factor_mem_of_mem_fibre C E i hB hE
    have hf := fromFactor_mem_fibre C i hB hother hd
    apply refined_eq_of_factor_and_complement_eq E _ i (fromFactor_factor C i hd).symm
    intro j hji
    exact ((Finset.mem_filter.mp hE).2 j hji).trans
      ((Finset.mem_filter.mp hf).2 j hji).symm

end Erdos387Proof.MediumFactorWindow
