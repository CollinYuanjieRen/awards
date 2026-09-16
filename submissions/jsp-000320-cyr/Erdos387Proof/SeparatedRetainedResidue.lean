import Erdos387Proof.SeparatedPrimeFibre
import Erdos387Proof.MediumFibreFourier
import Erdos387Proof.MaskedReciprocalPhase

/-! The fixed residue for the separated phase retains the small selected
factor r. Only q varies; in particular the fixed residue is congruent to the
selected index modulo r as well as to every complementary tuple index. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedRetainedResidue
open Erdos387 Erdos387.CoverBPZ ConvenientCertificateCover
open MediumComplementFourier IntegerClassFourier MediumReciprocalPhase
open SeparatedCertificateEnlargement MaskedReciprocalPhase
open scoped BigOperators

/-- Reassociate three coprime CRT moduli, retaining the same selected-index
residue on both factors of the split selected coordinate. -/
theorem simultaneousResidue_split_right {Q r q : ℕ}
    (hQ : 0 < Q) (hr : 0 < r) (hq : 0 < q)
    (hQr : Q.Coprime r) (hQq : Q.Coprime q) (hrq : r.Coprime q)
    (gamma i : ℕ) :
    simultaneousResidue (hQr.mul_right hQq) gamma i =
      simultaneousResidue (hQq.mul_left hrq)
        (simultaneousResidue hQr gamma i) i := by
  let l := simultaneousResidue (hQr.mul_right hQq) gamma i
  let v := simultaneousResidue (hQq.mul_left hrq)
    (simultaneousResidue hQr gamma i) i
  have hleftQ : Int.ModEq (Q : ℤ) (l : ℤ) (gamma : ℤ) :=
    Int.natCast_modEq_iff.mpr (simultaneousResidue_mod_left _ _ _)
  have hleftRQ : Nat.ModEq (r*q) l i := simultaneousResidue_mod_right _ _ _
  have hleftR : Int.ModEq (r : ℤ) (l : ℤ) (i : ℤ) :=
    Int.natCast_modEq_iff.mpr (hleftRQ.of_dvd (dvd_mul_right _ _))
  have hleftq : Int.ModEq (q : ℤ) (l : ℤ) (i : ℤ) :=
    Int.natCast_modEq_iff.mpr (hleftRQ.of_dvd (dvd_mul_left _ _))
  have hmod : Int.ModEq (Q*r*q : ℕ) (l : ℤ) (v : ℤ) := by
    apply (simultaneous_modEq_iff (hQq.mul_left hrq) _ _ _).mp
    exact ⟨(simultaneous_modEq_iff hQr _ _ _).mp ⟨hleftQ,hleftR⟩,hleftq⟩
  have hmodN : Nat.ModEq (Q*r*q) l v := Int.natCast_modEq_iff.mp hmod
  apply hmodN.eq_of_lt_of_lt
  · simpa only [Nat.mul_assoc] using
      simultaneousResidue_lt (hQr.mul_right hQq) hQ (Nat.mul_pos hr hq) gamma i
  · exact simultaneousResidue_lt (hQq.mul_left hrq) (Nat.mul_pos hQ hr) hq _ _

variable {B K X z y medium second gap g : ℕ} {S : BPZSection6Input B K}
variable {i : Fin S.k} {t : SplitCertificate S X}

noncomputable def retainedResidue (t : SplitCertificate S X) (i : Fin S.k)
    (g b : ℕ) (hg : (refinementModulus S*t.1.val.otherValue i).Coprime g)
    (hr : (refinementModulus S*t.1.val.otherValue i*g).Coprime t.2.1) : ℕ :=
  simultaneousResidue hr (combinedResidue t.1 i g b hg) i.val

theorem retainedResidue_mod_small (t : SplitCertificate S X) (i : Fin S.k)
    (g b : ℕ) (hg : (refinementModulus S*t.1.val.otherValue i).Coprime g)
    (hr : (refinementModulus S*t.1.val.otherValue i*g).Coprime t.2.1) :
    Nat.ModEq t.2.1 (retainedResidue t i g b hg hr) i.val :=
  simultaneousResidue_mod_right hr _ _

theorem retainedResidue_mod_factor (t : SplitCertificate S X) (i : Fin S.k)
    (g b : ℕ) (hg : (refinementModulus S*t.1.val.otherValue i).Coprime g)
    (hr : (refinementModulus S*t.1.val.otherValue i*g).Coprime t.2.1)
    (j : Fin S.k) (hji : j≠i) :
    Nat.ModEq (t.1.val.factor j) (retainedResidue t i g b hg hr) j.val := by
  have hD : Nat.ModEq (t.1.val.otherValue i)
      (retainedResidue t i g b hg hr) (t.1.val.otherResidue i) :=
    ((simultaneousResidue_mod_left hr _ _).of_dvd (by
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)).trans
      (combinedResidue_mod_otherValue t.1 i g b hg)
  exact (hD.of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr
    ⟨hji,Finset.mem_univ _⟩))).trans (t.1.val.otherResidue_mod_factor hji)

/-- This fixed residue is unchanged throughout a full complementary-vector,
small-factor fibre. The dyadic block is immaterial to the CRT identity. -/
theorem retainedResidue_eq_of_key (a t : SplitCertificate S X)
    (hkey : SameAnchorKey i t a) (b : ℕ)
    (haG : (refinementModulus S*a.1.val.otherValue i).Coprime g)
    (htG : (refinementModulus S*t.1.val.otherValue i).Coprime g)
    (haR : (refinementModulus S*a.1.val.otherValue i*g).Coprime a.2.1)
    (htR : (refinementModulus S*t.1.val.otherValue i*g).Coprime t.2.1) :
    retainedResidue t i g b htG htR = retainedResidue a i g b haG haR := by
  have hD := SeparatedPrimeFibre.otherValue_eq_of_key hkey
  have hgamma := combinedResidue_eq_of_factors_eq_off_index t.1 a.1 i g b htG haG
    ((MediumComplementGrouping.vector_eq_iff i t.1 a.1).mp hkey.1)
  simp only [retainedResidue,hD,hkey.2.1,hgamma]

/-- Complex Fourier terms transport across equal moduli and residues. -/
theorem fourierTerm_congr (X q₁ q₂ r₁ r₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (h : ℤ) (hq : q₁=q₂) (hr : r₁=r₂) :
    ZMod.stdAddChar (-(h : ZMod q₁)*(r₁ : ZMod q₁))*
      TentFourier.coefficient X q₁ (h : ZMod q₁) =
    ZMod.stdAddChar (-(h : ZMod q₂)*(r₂ : ZMod q₂))*
      TentFourier.coefficient X q₂ (h : ZMod q₂) := by
  subst q₂
  subst r₂
  rfl

/-- The reciprocal phase identity after retaining r in the fixed modulus.
Only the varying q is inverted, and its original unit mask is preserved. -/
theorem fourierSummand_eq_single (X Q q gamma i : ℕ) [NeZero Q] [NeZero q]
    (hcop : Q.Coprime q) (h : ℤ) :
    ZMod.stdAddChar (-(h : ZMod (Q*q))*
      (simultaneousResidue hcop gamma i : ZMod (Q*q))) *
        TentFourier.coefficient X (Q*q) (h : ZMod (Q*q)) =
      FourierVariation.tentWeight X h (-i) (Q*q : ℕ)⁻¹ *
        seq Q ((-h)*((gamma : ℤ)-i)) 0 [] (q : ℤ) := by
  have hu : IsUnit (q : ZMod Q) := (ZMod.isUnit_iff_coprime q Q).mpr hcop.symm
  have hh := MediumWeightedPhase.fourierSummand_eq_weightedCoefficient
    X Q 1 q gamma i (Nat.coprime_one_left Q) hcop.symm h
  have hterm := fourierTerm_congr X (Q*(1*q)) (Q*q) _ _ h
    (by rw [one_mul])
    (MediumFibreFourier.simultaneousResidue_congr
      ((Nat.coprime_one_left Q).symm.mul_right hcop) hcop gamma i rfl (one_mul q))
  apply hterm.symm.trans
  simpa only [one_mul,MediumWeightedPhase.reciprocalCoefficient,Nat.cast_one,
    ZMod.inv_one,mul_one,Kloosterman.coefficient,if_pos hu,seq,good,phase,zero_add,
    Int.cast_natCast] using hh

/-- All coprimality inputs to the retained CRT come from the actual
certificate and the actual small-prime sieve support. -/
theorem sieve_data (ht : t∈certificates S X z y medium second gap i)
    (hg : Squarefree g)
    (hsupport : ∀ p∈g.primeFactors, max (2*S.k) 3 ≤ p ∧ p < z) :
    (refinementModulus S*t.1.val.otherValue i).Coprime g ∧
    (refinementModulus S*t.1.val.otherValue i*g).Coprime t.2.1 ∧
    (refinementModulus S*t.1.val.otherValue i*g).Coprime t.2.2 ∧
    (refinementModulus S*t.1.val.value).Coprime g ∧
    (refinementModulus S*t.1.val.otherValue i*g*t.2.1).Coprime t.2.2 := by
  have hd := ConvenientPhaseData.sieve_applicability
    (mem_generic_split_enlargement ht) hg hsupport
  have hMDg := hd.2.2.1.symm
  have hr := hd.2.2.2.2.2.1.symm
  have hq := hd.2.2.2.2.2.2.symm
  have hgr : g.Coprime t.2.1 := hr.of_dvd_left (dvd_mul_left _ _)
  have hgq : g.Coprime t.2.2 := hq.of_dvd_left (dvd_mul_left _ _)
  refine ⟨hMDg,hr,hq,?_,hq.mul_left (admissible ht).selected_coprime⟩
  rw [← t.1.val.factor_mul_otherValue i,(admissible ht).factor]
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
    (hMDg.mul_left hgr.symm).mul_left hgq.symm

/-- Exact equality with the original certificate residue, not merely with
a newly invented phase. The retained residue includes the small r-class. -/
theorem certificateResidue_eq_retained
    (ht : t∈certificates S X z y medium second gap i)
    (hg : Squarefree g)
    (hsupport : ∀ p∈g.primeFactors, max (2*S.k) 3 ≤ p ∧ p < z)
    (b : ℕ) (hb : b < g) :
    let hd := sieve_data ht hg hsupport
    simultaneousResidue hd.2.2.2.1
      (simultaneousResidue t.1.property (refinementResidue S) t.1.val.crtResidue) b =
    simultaneousResidue hd.2.2.2.2
      (retainedResidue t i g b hd.1 hd.2.1) i.val := by
  let hd := sieve_data ht hg hsupport
  let : NeZero g := ⟨hg.ne_zero⟩
  have hbnd := split_bounds ht
  have hr0 : 0 < t.2.1 := by omega
  have hq0 : 0 < t.2.2 := by omega
  have hgd : g.Coprime (t.1.val.factor i) := by
    rw [(admissible ht).factor]
    exact (hd.2.1.of_dvd_left (dvd_mul_left _ _)).mul_right
      (hd.2.2.1.of_dvd_left (dvd_mul_left _ _))
  have hfirst := MediumFibreFourier.certificateResidue_eq_complementResidue
    t.1 i b hb hd.1 hd.2.2.2.1 hgd (combined_coprime_factor t.1 i hgd)
  dsimp only
  rw [hfirst]
  have hsplit := simultaneousResidue_split_right
    (Nat.mul_pos (Nat.mul_pos (refinementModulus_pos S) (t.1.val.otherValue_pos i))
      (Nat.pos_of_ne_zero hg.ne_zero)) hr0 hq0 hd.2.1 hd.2.2.1
        (admissible ht).selected_coprime (combinedResidue t.1 i g b hd.1) i.val
  simpa only [(admissible ht).factor,retainedResidue] using hsplit

/-- One actual certificate Fourier summand, transported to the fixed
retained conductor. This is the summand used by the original class expansion. -/
theorem certificate_fourierSummand_eq_single
    (ht : t∈certificates S X z y medium second gap i)
    (hg : Squarefree g)
    (hsupport : ∀ p∈g.primeFactors, max (2*S.k) 3 ≤ p ∧ p < z)
    (b : ℕ) (hb : b < g) (h : ℤ) :
    let hd := sieve_data ht hg hsupport
    let Q := refinementModulus S*t.1.val.otherValue i*g*t.2.1
    let : NeZero (refinementModulus S*t.1.val.value*g) :=
      ⟨Nat.ne_of_gt (Nat.mul_pos
        (Nat.mul_pos (refinementModulus_pos S) t.1.val.value_pos)
          (Nat.pos_of_ne_zero hg.ne_zero))⟩
    let : NeZero Q := ⟨Nat.ne_of_gt (Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (refinementModulus_pos S) (t.1.val.otherValue_pos i))
        (Nat.pos_of_ne_zero hg.ne_zero)) (by have hb := split_bounds ht; omega))⟩
    ZMod.stdAddChar (-(h : ZMod (refinementModulus S*t.1.val.value*g))*
      (simultaneousResidue hd.2.2.2.1
        (simultaneousResidue t.1.property (refinementResidue S) t.1.val.crtResidue) b :
          ZMod (refinementModulus S*t.1.val.value*g))) *
      TentFourier.coefficient X (refinementModulus S*t.1.val.value*g)
        (h : ZMod (refinementModulus S*t.1.val.value*g)) =
    FourierVariation.tentWeight X h (-i.val) (Q*t.2.2 : ℕ)⁻¹ *
      seq Q ((-h)*((retainedResidue t i g b hd.1 hd.2.1 : ℤ)-i.val)) 0 [] (t.2.2 : ℤ) := by
  have hbnd := split_bounds ht
  let : NeZero (refinementModulus S) := ⟨(refinementModulus_pos S).ne'⟩
  let : NeZero t.1.val.value := ⟨t.1.val.value_pos.ne'⟩
  let : NeZero (t.1.val.otherValue i) := ⟨(t.1.val.otherValue_pos i).ne'⟩
  let : NeZero g := ⟨hg.ne_zero⟩
  let : NeZero t.2.1 := ⟨by omega⟩
  dsimp only
  let : NeZero t.2.2 := ⟨by omega⟩
  have hmod : refinementModulus S*t.1.val.value*g =
      (refinementModulus S*t.1.val.otherValue i*g*t.2.1)*t.2.2 := by
    rw [← t.1.val.factor_mul_otherValue i,(admissible ht).factor]
    ring
  have hh := fourierTerm_congr X _ _ _ _ h hmod
    (certificateResidue_eq_retained ht hg hsupport b hb)
  rw [hh]
  exact fourierSummand_eq_single X _ _ _ _ (sieve_data ht hg hsupport).2.2.2.2 h

/-- The original finite Fourier summand, with proof-only applicability data. -/
noncomputable def actualTerm
    (ht : t∈certificates S X z y medium second gap i)
    (hg : Squarefree g)
    (hsupport : ∀ p∈g.primeFactors, max (2*S.k) 3 ≤ p ∧ p < z)
    (b : ℕ) (h : ℤ) : ℂ := by
  letI : NeZero (refinementModulus S*t.1.val.value*g) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos
      (Nat.mul_pos (refinementModulus_pos S) t.1.val.value_pos)
        (Nat.pos_of_ne_zero hg.ne_zero))⟩
  exact ZMod.stdAddChar (-(h : ZMod (refinementModulus S*t.1.val.value*g))*
      (simultaneousResidue (sieve_data ht hg hsupport).2.2.2.1
        (simultaneousResidue t.1.property (refinementResidue S) t.1.val.crtResidue) b :
          ZMod (refinementModulus S*t.1.val.value*g))) *
      TentFourier.coefficient X (refinementModulus S*t.1.val.value*g)
        (h : ZMod (refinementModulus S*t.1.val.value*g))

end Erdos387Proof.SeparatedRetainedResidue
