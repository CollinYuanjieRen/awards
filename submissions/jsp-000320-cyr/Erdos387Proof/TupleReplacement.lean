import Erdos387Proof.ComplementResidue
import Erdos387Proof.MediumCertificateCover

/-! Replacing one tuple coordinate gives the exact independent varying
factor domain used when grouping the signed medium sieve sum. -/

namespace Erdos387Proof.TupleReplacement

open Erdos387
open scoped BigOperators

noncomputable def replace {k X : ℕ} (C : TupleCertificate k X) (i : Fin k)
    (d : ℕ) (hd : 0 < d) (hdX : d ≤ X) (hcop : Nat.Coprime d (C.otherValue i)) :
    TupleCertificate k X := by
  classical
  let f : Fin k → Fin (X + 1) := Function.update C.val i ⟨d, by omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [f] using hd
    · simpa [f, hji, TupleCertificate.factor] using C.positive j
  · intro a b hab
    by_cases hai : a = i
    · subst a
      have hbi : b ≠ i := Ne.symm hab
      simpa [f, hbi, TupleCertificate.factor] using
        Nat.Coprime.of_dvd_right (C.factor_dvd_otherValue hbi) hcop
    · by_cases hbi : b = i
      · subst b
        simpa [f, hai, TupleCertificate.factor] using
          (Nat.Coprime.of_dvd_right (C.factor_dvd_otherValue hai) hcop).symm
      · simpa [f, hai, hbi, TupleCertificate.factor] using C.pairwise a b hab

theorem factor_replace {k X : ℕ} (C : TupleCertificate k X) (i : Fin k)
    (d : ℕ) (hd : 0 < d) (hdX : d ≤ X) (hcop : Nat.Coprime d (C.otherValue i))
    (j : Fin k) :
    (replace C i d hd hdX hcop).factor j = if j = i then d else C.factor j := by
  classical
  by_cases hji : j = i <;> simp [replace, TupleCertificate.factor, hji]

theorem otherValue_replace {k X : ℕ} (C : TupleCertificate k X) (i : Fin k)
    (d : ℕ) (hd : 0 < d) (hdX : d ≤ X) (hcop : Nat.Coprime d (C.otherValue i)) :
    (replace C i d hd hdX hcop).otherValue i = C.otherValue i := by
  apply otherValue_eq_of_factors_eq_off_index
  intro j hji
  simp [factor_replace, hji]

theorem otherResidue_replace {k X : ℕ} (C : TupleCertificate k X) (i : Fin k)
    (d : ℕ) (hd : 0 < d) (hdX : d ≤ X) (hcop : Nat.Coprime d (C.otherValue i)) :
    (replace C i d hd hdX hcop).otherResidue i = C.otherResidue i := by
  apply otherResidue_eq_of_factors_eq_off_index
  intro j hji
  simp [factor_replace, hji]

theorem value_replace {k X : ℕ} (C : TupleCertificate k X) (i : Fin k)
    (d : ℕ) (hd : 0 < d) (hdX : d ≤ X) (hcop : Nat.Coprime d (C.otherValue i)) :
    (replace C i d hd hdX hcop).value = d * C.otherValue i := by
  rw [← (replace C i d hd hdX hcop).factor_mul_otherValue i,
    factor_replace, if_pos rfl, otherValue_replace]

theorem eq_of_factors_eq {k X : ℕ} {C D : TupleCertificate k X}
    (h : ∀ j, C.factor j = D.factor j) : C = D := by
  apply Subtype.ext
  funext j
  exact Fin.ext (h j)

/-- Within a fixed complementary vector, the varying factor identifies
the entire refined certificate, including its proof fields. -/
theorem refined_eq_of_factor_and_complement_eq {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C D : RefinedTupleCertificate S X)
    (i : Fin S.k) (hi : C.val.factor i = D.val.factor i)
    (hother : ∀ j, j ≠ i → C.val.factor j = D.val.factor j) : C = D := by
  apply Subtype.ext
  apply eq_of_factors_eq
  intro j
  by_cases hji : j = i
  · simpa [hji] using hi
  · exact hother j hji

noncomputable def replaceRefined {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (d : ℕ)
    (hd : 0 < d) (hdX : d ≤ X)
    (hcop : Nat.Coprime d (CoverBPZ.refinementModulus S * C.val.otherValue i)) :
    RefinedTupleCertificate S X := by
  let C' := replace C.val i d hd hdX (hcop.of_dvd_right (dvd_mul_left _ _))
  refine ⟨C', ?_⟩
  dsimp [C']
  rw [value_replace]
  apply Nat.Coprime.mul_right (hcop.of_dvd_right (dvd_mul_right _ _)).symm
  exact C.property.of_dvd_right (by
    rw [← C.val.factor_mul_otherValue i]
    exact dvd_mul_left _ _)

theorem factor_replaceRefined {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (d : ℕ)
    (hd : 0 < d) (hdX : d ≤ X)
    (hcop : Nat.Coprime d (CoverBPZ.refinementModulus S * C.val.otherValue i))
    (j : Fin S.k) :
    (replaceRefined C i d hd hdX hcop).val.factor j =
      if j = i then d else C.val.factor j :=
  factor_replace C.val i d hd hdX (hcop.of_dvd_right (dvd_mul_left _ _)) j

theorem value_replaceRefined {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (d : ℕ)
    (hd : 0 < d) (hdX : d ≤ X)
    (hcop : Nat.Coprime d (CoverBPZ.refinementModulus S * C.val.otherValue i)) :
    (replaceRefined C i d hd hdX hcop).val.value = d * C.val.otherValue i :=
  value_replace C.val i d hd hdX (hcop.of_dvd_right (dvd_mul_left _ _))

/-- Exact varying-coordinate membership; roughness and squarefreeness of
the replaced coordinate do not occur in this enlarged parameter space. -/
theorem replaceRefined_mem_certificates_iff {B K X z medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (d : ℕ)
    (hd : 0 < d) (hdX : d ≤ X)
    (hcop : Nat.Coprime d (CoverBPZ.refinementModulus S * C.val.otherValue i))
    (hother : ∀ j, j ≠ i → Squarefree (C.val.factor j) ∧ IsZRough z (C.val.factor j)) :
    replaceRefined C i d hd hdX hcop ∈
        MediumCertificateCover.certificates S X z medium large i ↔
      d * C.val.otherValue i ≤ X ∧ X / 2 < B * (d * C.val.otherValue i) ∧
        medium < d ∧ d ≤ large := by
  classical
  simp only [MediumCertificateCover.certificates, Finset.mem_filter,
    Finset.mem_univ, true_and, value_replaceRefined, factor_replaceRefined, ite_true]
  constructor
  · rintro ⟨h1, h2, h3, h4, hrest⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    intro j hji
    simpa only [if_neg hji] using hother j hji

end Erdos387Proof.TupleReplacement
