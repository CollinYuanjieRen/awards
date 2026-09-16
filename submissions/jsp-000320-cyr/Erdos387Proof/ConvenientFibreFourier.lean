import Erdos387Proof.ConvenientPartialFourier
import Erdos387Proof.ConvenientSplitFibre
import Erdos387Proof.MediumFibreFourier

/-!
# Exact convenient-range Fourier transport in one complement fibre

The actual finite nonzero Fourier partial is first reassociated from the full
certificate CRT modulus to `Q * r * s`, where
`Q = refinementModulus S * D * g`.  The complementary vector fixes `D` and
the combined residue `gamma`; only the ordered inner-fibre pair `(r,s)` varies.
All equalities precede absolute values or moment estimates.
-/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientFibreFourier

open Erdos387 Erdos387.CoverBPZ
open ConvenientCertificateCover ConvenientComplementGrouping
open ConvenientSplitFibre ConvenientPhaseData ConvenientFourierTail
open IntegerSieveResidues MediumComplementFourier MediumComplementGrouping
open MediumFibreFourier MediumPartialFourier
open scoped BigOperators

noncomputable abbrev Certificates {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium : ℕ) (i : Fin S.k) :=
  ConvenientCertificateEnlargement.certificates S X z y medium i

noncomputable def fibreCertificate {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    {c : {c // c ∈ complementVectorsOf i (Certificates S X z y medium i)}}
    (p : {p // p ∈ splitPairFibreOf i
      (Certificates S X z y medium i) c.val}) : SplitCertificate S X :=
  pairRepresentativeOf c p

theorem fibreCertificate_mem {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    {c : {c // c ∈ complementVectorsOf i (Certificates S X z y medium i)}}
    (p : {p // p ∈ splitPairFibreOf i
      (Certificates S X z y medium i) c.val}) :
    fibreCertificate p ∈ Certificates S X z y medium i :=
  pairRepresentativeOf_mem c p

theorem fibreCertificate_pair {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    {c : {c // c ∈ complementVectorsOf i (Certificates S X z y medium i)}}
    (p : {p // p ∈ splitPairFibreOf i
      (Certificates S X z y medium i) c.val}) :
    (fibreCertificate p).2 = p.val :=
  pairRepresentativeOf_pair c p

theorem fibreCertificate_off_factors {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    {c : {c // c ∈ complementVectorsOf i (Certificates S X z y medium i)}}
    (p : {p // p ∈ splitPairFibreOf i
      (Certificates S X z y medium i) c.val}) :
    ∀ j, j ≠ i → (fibreCertificate p).1.val.factor j =
      (complementRepresentative c).1.val.factor j := by
  exact (vector_eq_iff i (fibreCertificate p).1
    (complementRepresentative c).1).mp
      ((pairRepresentativeOf_vector c p).trans
        (vector_complementRepresentative c).symm)

/-- The finite bilinear Fourier partial with the modulus and phase fixed by
the complement.  The guards are only the actual prime-subset domain; the
certificate and ordered pair are already carried by subtype indices. -/
noncomputable def complementMaskedPartial {B K X z y medium : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i (Certificates S X z y medium i)})
    (p : {p // p ∈ splitPairFibreOf i
      (Certificates S X z y medium i) c.val})
    (H : ℕ) (T : Finset ℕ) : ℝ := by
  classical
  exact if hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset then
    by
      let t := fibreCertificate p
      let C₀ := (complementRepresentative c).1
      let g := ∏ q ∈ T, q
      have hk : 0 < S.k := by have := S.hk3; omega
      have hg := (windowProduct_data hk hT).1
      have hsupport := (windowProduct_data hk hT).2
      have ht := fibreCertificate_mem p
      have hbase := complementRepresentative_mem c
      have hdata := sieve_applicability ht hg hsupport
      have hbaseData := sieve_applicability hbase hg hsupport
      have hpair := fibreCertificate_pair p
      have hD : t.1.val.otherValue i = C₀.val.otherValue i :=
        otherValue_eq_of_factors_eq_off_index t.1.val C₀.val i
          (fibreCertificate_off_factors p)
      let Q := refinementModulus S * C₀.val.otherValue i * g
      have hrQ : p.val.1.Coprime Q := by
        simpa only [t,C₀,g,Q,hpair,hD,Nat.mul_assoc] using
          hdata.2.2.2.2.2.1
      have hr0 : 0 < p.val.1 := by
        simpa only [t,hpair] using (ConvenientPhaseData.split_pos ht).1
      have hs0 : 0 < p.val.2 := by
        simpa only [t,hpair] using (ConvenientPhaseData.split_pos ht).2
      have hDv : (refinementModulus S * C₀.val.otherValue i).Coprime g :=
        hbaseData.2.2.1.symm
      letI : NeZero g := ⟨hg.ne_zero⟩
      letI : NeZero Q := ⟨(Nat.mul_pos
        (Nat.mul_pos (refinementModulus_pos S) (C₀.val.otherValue_pos i))
        (NeZero.pos g)).ne'⟩
      letI : NeZero p.val.1 := ⟨hr0.ne'⟩
      exact ∑ a ∈ localAssignmentResidues g S.k,
        ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
          (MediumWeightedPhase.maskedFourierSummand X Q p.val.1
            (combinedResidue C₀ i g a hDv) i.val hrQ h p.val.2 hs0).re
  else 0

set_option linter.style.haveILetI false in
/-- Exact full-CRT to complement-fixed bilinear transport for one actual
ordered split pair. -/
theorem partialRemainder_eq_complementMaskedPartial
    {B K X z y medium H : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i (Certificates S X z y medium i)})
    (p : {p // p ∈ splitPairFibreOf i
      (Certificates S X z y medium i) c.val})
    {T : Finset ℕ} (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset)
    (hX : 0 < X)
    (hHq : 2 * H < refinementModulus S * (fibreCertificate p).1.val.value *
      (∏ q ∈ T, q)) :
    ConvenientPartialFourier.partialRemainder i (fibreCertificate p)
        z y medium H T = complementMaskedPartial c p H T := by
  classical
  let t := fibreCertificate p
  let C₀ := (complementRepresentative c).1
  let g := ∏ q ∈ T, q
  have hk : 0 < S.k := by have := S.hk3; omega
  have hg := (windowProduct_data hk hT).1
  have hsupport := (windowProduct_data hk hT).2
  have ht := fibreCertificate_mem p
  have hbase := complementRepresentative_mem c
  have hdata := sieve_applicability ht hg hsupport
  have hbaseData := sieve_applicability hbase hg hsupport
  have hpair := fibreCertificate_pair p
  have hoff := fibreCertificate_off_factors p
  have hD : t.1.val.otherValue i = C₀.val.otherValue i :=
    otherValue_eq_of_factors_eq_off_index t.1.val C₀.val i hoff
  have hfactor : t.1.val.factor i = p.val.1 * p.val.2 := by
    simpa only [hpair] using ConvenientCertificateEnlargement.factor_eq ht
  have hDv₁ : (refinementModulus S * t.1.val.otherValue i).Coprime g :=
    hdata.2.2.1.symm
  have hDv₀ : (refinementModulus S * C₀.val.otherValue i).Coprime g :=
    hbaseData.2.2.1.symm
  have hfull := certificateClassModulus_coprime ht hg hsupport
  have hrQ₁ : p.val.1.Coprime
      (refinementModulus S * (t.1.val.otherValue i * g)) := by
    simpa only [hpair,Nat.mul_assoc] using hdata.2.2.2.2.2.1
  have hsQ₁ : p.val.2.Coprime
      (refinementModulus S * (t.1.val.otherValue i * g)) := by
    simpa only [hpair,Nat.mul_assoc] using hdata.2.2.2.2.2.2
  have hr0 : 0 < p.val.1 := by
    simpa only [hpair] using (ConvenientPhaseData.split_pos ht).1
  have hs0 : 0 < p.val.2 := by
    simpa only [hpair] using (ConvenientPhaseData.split_pos ht).2
  let Q₁ := refinementModulus S * (t.1.val.otherValue i * g)
  let Q₀ := refinementModulus S * C₀.val.otherValue i * g
  have hQ : Q₁ = Q₀ := by simp only [Q₁,Q₀,hD,Nat.mul_assoc]
  have hrQ₀ : p.val.1.Coprime Q₀ := by simpa only [Q₀,← hQ] using hrQ₁
  letI : NeZero g := ⟨hg.ne_zero⟩
  letI : NeZero p.val.1 := ⟨hr0.ne'⟩
  letI : NeZero p.val.2 := ⟨hs0.ne'⟩
  letI : NeZero Q₁ := ⟨(Nat.mul_pos
    (refinementModulus_pos S)
      (Nat.mul_pos (t.1.val.otherValue_pos i) (NeZero.pos g))).ne'⟩
  letI : NeZero Q₀ := ⟨hQ ▸ NeZero.ne Q₁⟩
  rw [ConvenientPartialFourier.partialRemainder_eq_nonzeroPartial
    ht hT hX hHq]
  rw [MediumFibreFourier.certificateNonzeroPartial_eq_masked t.1 i
    hfactor hg hDv₁ hfull hrQ₁ hsQ₁]
  unfold complementMaskedPartial
  rw [dif_pos hT]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg Complex.re
  have hgamma : combinedResidue t.1 i g a hDv₁ =
      combinedResidue C₀ i g a hDv₀ :=
    MediumComplementFourier.combinedResidue_eq_of_factors_eq_off_index
      t.1 C₀ i g a hDv₁ hDv₀ hoff
  exact MediumFibreFourier.maskedFourierSummand_congr
    X Q₁ Q₀ p.val.1 _ _ i hrQ₁ hrQ₀ h p.val.2 hs0 hQ hgamma

/-- The complete ordered split-pair fibre transports before any triangle
inequality.  An arbitrary scalar weight may retain both hyperbola masks and
all later finite separator coefficients outside the moment indices. -/
theorem sum_fibre_partialRemainder_eq_complementMaskedPartial
    {B K X z y medium H : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k}
    (c : {c // c ∈ complementVectorsOf i (Certificates S X z y medium i)})
    {T : Finset ℕ} (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset)
    (hX : 0 < X)
    (hHq : ∀ p : {p // p ∈ splitPairFibreOf i
      (Certificates S X z y medium i) c.val},
        2 * H < refinementModulus S *
          (fibreCertificate p).1.val.value * (∏ q ∈ T, q))
    (w : ℕ × ℕ → ℝ) :
    (∑ p ∈ (splitPairFibreOf i
        (Certificates S X z y medium i) c.val).attach,
      w p.val * ConvenientPartialFourier.partialRemainder i
        (fibreCertificate p) z y medium H T) =
      ∑ p ∈ (splitPairFibreOf i
        (Certificates S X z y medium i) c.val).attach,
        w p.val * complementMaskedPartial c p H T := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg (fun a : ℝ => w p.val * a)
  exact partialRemainder_eq_complementMaskedPartial c p hT hX
    (hHq p)

end Erdos387Proof.ConvenientFibreFourier
