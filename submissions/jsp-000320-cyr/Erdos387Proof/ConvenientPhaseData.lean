import Erdos387Proof.ConvenientCertificateEnlargement
import Erdos387Proof.MediumWeightedPhase

/-! Exact arithmetic applicability for the convenient-range reciprocal phase.
The sieve support is below the roughness threshold. The canonical complementary
residue, and hence the integer phase coefficient, is unchanged when only the
selected factor and its ordered factorization change. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientPhaseData
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open ConvenientCertificateEnlargement MediumComplementFourier
open scoped BigOperators

/-- A number supported below the roughness threshold is coprime to every
rough number. The support statement excludes zero via the explicit hypothesis. -/
theorem coprime_of_support_rough {g z d : ℕ} (hg : g≠0)
    (hsupport : ∀ p ∈ g.primeFactors, p<z) (hd : IsZRough z d) :
    g.Coprime d := by
  by_contra hcop
  obtain ⟨p,hp,hpg,hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  exact hd p hp (hsupport p (Nat.mem_primeFactors.mpr ⟨hp,hpg,hg⟩)) hpd

/-- All fixed-modulus and separate-variable coprimality follows from the
actual enlarged certificate and the sieve support. No mutual coprimality of
r and s is required. -/
theorem sieve_applicability {B K X z y medium g : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t∈ConvenientCertificateEnlargement.certificates S X z y medium i) (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors, max (2*S.k) 3≤p ∧ p<z) :
    let D := t.1.val.otherValue i
    Squarefree D ∧ IsZRough z D ∧
      g.Coprime (refinementModulus S*D) ∧ Squarefree (D*g) ∧
      (refinementModulus S).Coprime (D*g) ∧
      t.2.1.Coprime (refinementModulus S*D*g) ∧
      t.2.2.Coprime (refinementModulus S*D*g) := by
  dsimp only
  obtain ⟨hDsq,hDr,hr,hs,hrMD,hsMD⟩ := retained_data ht
  have hgp := fun p hp => (hsupport p hp).2
  have hgD := coprime_of_support_rough hg.ne_zero hgp hDr
  have hgr := coprime_of_support_rough hg.ne_zero hgp hr
  have hgs := coprime_of_support_rough hg.ne_zero hgp hs
  have hMg : (refinementModulus S).Coprime g := by
    by_contra hcop
    obtain ⟨p,hp,hpM,hpg⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hlo := (le_max_left (2*S.k) 3).trans
      (hsupport p (Nat.mem_primeFactors.mpr ⟨hp,hpg,hg.ne_zero⟩)).1
    have hhi := prime_lt_two_mul_k_of_dvd_refinementModulus S hp hpM
    omega
  have hMD := fixed_complement_coprime t.1 i
  exact ⟨hDsq,hDr,hMg.symm.mul_right hgD,
    (Nat.squarefree_mul hgD.symm).mpr ⟨hDsq,hg⟩,
    hMD.mul_right hMg,hrMD.mul_right hgr.symm,hsMD.mul_right hgs.symm⟩

/-- Rough complementary primes cannot identify two distinct tuple indices.
The sieve residue is arbitrary; it affects no congruence modulo D. -/
theorem gcd_combinedResidue_sub_index_eq_one
    {B K X z y medium g a : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t∈ConvenientCertificateEnlargement.certificates S X z y medium i) (hkz : S.k≤z)
    (hcop : (refinementModulus S*t.1.val.otherValue i).Coprime g) :
    Int.gcd ((combinedResidue t.1 i g a hcop : ℤ)-i.val)
      (t.1.val.otherValue i : ℤ)=1 := by
  let gamma := combinedResidue t.1 i g a hcop
  have hrough := (retained_data ht).2.1
  have hgamma := MediumReciprocalPhase.combinedResidue_mod_otherValue t.1 i g a hcop
  apply int_gcd_eq_one_of_no_prime_common
  intro p hp hpDiff hpD
  have hpDNat : p∣t.1.val.otherValue i := by exact_mod_cast hpD
  have hpLower : z≤p := by
    by_contra hpz
    exact hrough p hp (by omega) hpDNat
  have hgammaI : gamma≡i.val [MOD p] := by
    rw [Nat.modEq_iff_dvd]
    have hneg : (p : ℤ)∣-((gamma : ℤ)-i.val) := dvd_neg.mpr hpDiff
    simpa only [neg_sub] using hneg
  have hgammaOther : gamma≡t.1.val.otherResidue i [MOD p] :=
    hgamma.of_dvd hpDNat
  have hotherI : t.1.val.otherResidue i≡i.val [MOD p] :=
    hgammaOther.symm.trans hgammaI
  unfold TupleCertificate.otherValue at hpDNat
  obtain ⟨j,hj,hpj⟩ := (hp.prime.dvd_finsetProd_iff t.1.val.factor).mp hpDNat
  have hji : j≠i := (Finset.mem_erase.mp hj).1
  have hotherJ : t.1.val.otherResidue i≡j.val [MOD p] :=
    (t.1.val.otherResidue_mod_factor hji).of_dvd hpj
  have hij : i.val≡j.val [MOD p] := hotherI.symm.trans hotherJ
  exact hji (Fin.ext (hij.eq_of_lt_of_lt
    (i.isLt.trans_le (hkz.trans hpLower))
    (j.isLt.trans_le (hkz.trans hpLower))).symm)

/-- The fixed integer difference is unchanged under replacement of the
selected coordinate, including replacement of its ordered split pair. -/
theorem phaseDifference_eq_of_same_complement
    {B K X g a : ℕ} {S : BPZSection6Input B K} (i : Fin S.k)
    (t u : SplitCertificate S X)
    (ht : (refinementModulus S*t.1.val.otherValue i).Coprime g)
    (hu : (refinementModulus S*u.1.val.otherValue i).Coprime g)
    (hfactor : ∀ j, j≠i → t.1.val.factor j=u.1.val.factor j) :
    (combinedResidue t.1 i g a ht : ℤ)-i.val =
      (combinedResidue u.1 i g a hu : ℤ)-i.val := by
  rw [combinedResidue_eq_of_factors_eq_off_index t.1 u.1 i g a ht hu hfactor]

/-- Exact bilinear inverse phase, with the full small phase kept inside the
tent weight. The fixed integer coefficient is (-h)*(gamma-i). -/
theorem fourierSummand_eq_bilinear
    (X Q r s gamma i : ℕ) [NeZero Q] [NeZero r] [NeZero s]
    (hr : r.Coprime Q) (hs : s.Coprime Q) (h : ℤ) :
    let hcop : Q.Coprime (r*s) := hr.symm.mul_right hs.symm
    ZMod.stdAddChar (-(h : ZMod (Q*(r*s)))*
        (simultaneousResidue hcop gamma i : ZMod (Q*(r*s)))) *
      TentFourier.coefficient X (Q*(r*s)) (h : ZMod (Q*(r*s))) =
    FourierVariation.tentWeight X h (-i) (Q*(r*s) : ℕ)⁻¹ *
      ZMod.stdAddChar ((((-h)*((gamma : ℤ)-i) : ℤ) : ZMod Q)*
        (r : ZMod Q)⁻¹*(s : ZMod Q)⁻¹) := by
  dsimp only
  rw [MediumWeightedPhase.fourierSummand_eq_weightedCoefficient X Q r s gamma i hr hs h]
  rw [Kloosterman.coefficient,if_pos ((ZMod.isUnit_iff_coprime s Q).mpr hs)]
  rfl

theorem split_pos {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t∈ConvenientCertificateEnlargement.certificates S X z y medium i) : 0<t.2.1 ∧ 0<t.2.2 := by
  classical
  have hm := (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2
  obtain ⟨hr,hs⟩ := Finset.mem_product.mp hm
  exact ⟨(Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hr).1,
    (Nat.zero_le y).trans_lt (Finset.mem_Ioc.mp hs).1⟩

/-- The exact generic identity applies to the actual enlarged certificate.
Every unit and nonzero-modulus instance is discharged internally. -/
theorem certificate_fourierSummand_eq_bilinear
    {B K X z y medium g a : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} {t : SplitCertificate S X}
    (ht : t∈ConvenientCertificateEnlargement.certificates S X z y medium i) (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors, max (2*S.k) 3≤p ∧ p<z) (h : ℤ) :
    letI : NeZero (refinementModulus S) := ⟨(refinementModulus_pos S).ne'⟩
    letI : NeZero (t.1.val.otherValue i) := ⟨(t.1.val.otherValue_pos i).ne'⟩
    letI : NeZero g := ⟨hg.ne_zero⟩
    letI : NeZero t.2.1 := ⟨(split_pos ht).1.ne'⟩
    letI : NeZero t.2.2 := ⟨(split_pos ht).2.ne'⟩
    let Q := refinementModulus S*t.1.val.otherValue i*g
    let hdata := sieve_applicability ht hg hsupport
    let hcop := hdata.2.2.1.symm
    let gamma := combinedResidue t.1 i g a hcop
    let hsplit : Q.Coprime (t.2.1*t.2.2) :=
      hdata.2.2.2.2.2.1.symm.mul_right hdata.2.2.2.2.2.2.symm
    ZMod.stdAddChar (-(h : ZMod (Q*(t.2.1*t.2.2)))*
        (simultaneousResidue hsplit gamma i.val : ZMod (Q*(t.2.1*t.2.2)))) *
      TentFourier.coefficient X (Q*(t.2.1*t.2.2)) (h : ZMod (Q*(t.2.1*t.2.2))) =
    FourierVariation.tentWeight X h (-i.val) (Q*(t.2.1*t.2.2) : ℕ)⁻¹ *
      ZMod.stdAddChar ((((-h)*((gamma : ℤ)-i.val) : ℤ) : ZMod Q)*
        (t.2.1 : ZMod Q)⁻¹*(t.2.2 : ZMod Q)⁻¹) := by
  classical
  dsimp only
  have : NeZero (refinementModulus S) := ⟨(refinementModulus_pos S).ne'⟩
  have : NeZero (t.1.val.otherValue i) := ⟨(t.1.val.otherValue_pos i).ne'⟩
  have : NeZero g := ⟨hg.ne_zero⟩
  have : NeZero t.2.1 := ⟨(split_pos ht).1.ne'⟩
  have : NeZero t.2.2 := ⟨(split_pos ht).2.ne'⟩
  exact fourierSummand_eq_bilinear _ _ _ _ _ _
    (sieve_applicability ht hg hsupport).2.2.2.2.2.1
    (sieve_applicability ht hg hsupport).2.2.2.2.2.2 h

/-- Reduction modulo a multiple of D preserves the gcd with D. -/
theorem gcd_val_intCast_of_dvd {D Q : ℕ} [NeZero Q]
    (hD : 0<D) (hDQ : D∣Q) (a : ℤ) :
    Nat.gcd (a : ZMod Q).val D=Int.gcd a D := by
  have : NeZero D := ⟨hD.ne'⟩
  have hmod : Nat.ModEq D (a : ZMod Q).val (a : ZMod D).val := by
    rw [← ZMod.natCast_eq_natCast_iff]
    calc
      ((a : ZMod Q).val : ZMod D) =
          ZMod.castHom hDQ (ZMod D) ((a : ZMod Q).val : ZMod Q) := by
        simp only [map_natCast]
      _ = ZMod.castHom hDQ (ZMod D) (a : ZMod Q) := by
        rw [ZMod.natCast_zmod_val]
      _ = (a : ZMod D) := by simp only [map_intCast]
      _ = ((a : ZMod D).val : ZMod D) := (ZMod.natCast_zmod_val _).symm
  rw [hmod.gcd_eq]
  exact MediumReciprocalPhase.gcd_val_intCast D a

/-- Transfer only the sign of the Fourier frequency to a fixed unit scale.
The moment frequency is the small natural number |h|, not an arbitrary
representative of the full product coefficient modulo Q. -/
noncomputable def momentScale (Q : ℕ) (h delta : ℤ) : ℕ :=
  (if h<0 then (delta : ZMod Q) else (-delta : ZMod Q)).val

theorem momentScale_coprime {D Q : ℕ} [NeZero Q] (hD : 0<D)
    (hDQ : D∣Q) (h delta : ℤ) (hdelta : Int.gcd delta D=1) :
    (momentScale Q h delta).Coprime D := by
  unfold momentScale
  split_ifs
  · rw [Nat.coprime_iff_gcd_eq_one,gcd_val_intCast_of_dvd hD hDQ]
    exact hdelta
  · rw [Nat.coprime_iff_gcd_eq_one]
    rw [← Int.cast_neg,gcd_val_intCast_of_dvd hD hDQ]
    change Nat.gcd (-delta).natAbs D=1
    change Nat.gcd delta.natAbs D=1 at hdelta
    simpa only [Int.natAbs_neg] using hdelta

theorem frequency_mul_momentScale (Q : ℕ) [NeZero Q] (h delta : ℤ) :
    (h.natAbs : ZMod Q)*(momentScale Q h delta : ZMod Q)=
      (((-h)*delta : ℤ) : ZMod Q) := by
  have habs : (h.natAbs : ZMod Q)=((|h| : ℤ) : ZMod Q) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ZMod Q)) (Int.natCast_natAbs h)
  unfold momentScale
  by_cases hh : h<0
  · rw [if_pos hh,ZMod.natCast_zmod_val,habs,abs_of_neg hh]
    push_cast
    ring
  · rw [if_neg hh,ZMod.natCast_zmod_val,habs,abs_of_nonneg (by omega : 0≤h)]
    push_cast
    ring

end Erdos387Proof.ConvenientPhaseData
