import Erdos387Proof.MediumComplementFourier
import Erdos387Proof.PeriodicCompletion
import ErdosProblems.Erdos387.KloostermanMultiplicativity

/-!
# Reciprocal phases for the medium-factor argument

This file isolates the exact CRT identity and the local gcd estimate used
after writing the varying factor as `d = u*t`.  The complementary modulus
is `D`, the remaining sieve modulus is `v`, and the squarefree factor seen
by the Kloosterman estimate is `D*v`.  No coprimality of the frequency with
`v` is required.
-/

namespace Erdos387Proof.MediumReciprocalPhase

open Erdos387
open scoped BigOperators

/-- The complementary product in the enlarged medium cover remains
squarefree, even though squarefreeness of the varying coordinate was
deliberately discarded before the signed sieve expansion. -/
theorem certificate_otherValue_squarefree
    {B K X z medium large : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hC : C ∈ MediumCertificateCover.certificates S X z medium large i) :
    Squarefree (C.val.otherValue i) := by
  classical
  have hoff := (Finset.mem_filter.mp hC).2.2.2.2.2
  unfold TupleCertificate.otherValue
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a _ha b _hb hab
    change IsRelPrime (C.val.factor a) (C.val.factor b)
    rw [← Nat.coprime_iff_isRelPrime]
    exact C.val.pairwise a b hab
  · intro j hj
    exact (hoff j (Finset.mem_erase.mp hj).1).1

/-- Every prime in the complementary product retains the original rough
lower bound. -/
theorem certificate_otherValue_rough
    {B K X z medium large : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hC : C ∈ MediumCertificateCover.certificates S X z medium large i) :
    IsZRough z (C.val.otherValue i) := by
  classical
  have hoff := (Finset.mem_filter.mp hC).2.2.2.2.2
  intro p hp hpz hpD
  unfold TupleCertificate.otherValue at hpD
  obtain ⟨j, hj, hpj⟩ := (hp.prime.dvd_finsetProd_iff C.val.factor).mp hpD
  exact (hoff j (Finset.mem_erase.mp hj).1).2 p hp hpz hpj

/-- The refinement modulus remains coprime to the complementary product. -/
theorem certificate_refinementModulus_coprime_otherValue
    {B K X z medium large : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (_hC : C ∈ MediumCertificateCover.certificates S X z medium large i) :
    Nat.Coprime (CoverBPZ.refinementModulus S) (C.val.otherValue i) :=
  MediumComplementFourier.fixed_complement_coprime C i

/-- Exact applicability data for an enlarged medium certificate and a
squarefree sieve support lying below `z`. -/
theorem certificate_sieve_complement_applicability
    {B K X z medium large g : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hC : C ∈ MediumCertificateCover.certificates S X z medium large i)
    (hgSq : Squarefree g)
    (hgSupport : ∀ p ∈ g.primeFactors,
      max (2 * S.k) 3 ≤ p ∧ p < z) :
    let D := C.val.otherValue i
    IsZRough z D ∧ Squarefree D ∧ Nat.Coprime g D ∧
      Nat.Coprime (CoverBPZ.refinementModulus S) D ∧
      Nat.Coprime g (CoverBPZ.refinementModulus S * D) ∧
      Squarefree (g * D) ∧
      Nat.Coprime (CoverBPZ.refinementModulus S) (g * D) := by
  dsimp only
  have hDrough := certificate_otherValue_rough hC
  have hDsq := certificate_otherValue_squarefree hC
  have hMD := certificate_refinementModulus_coprime_otherValue hC
  have hgD : Nat.Coprime g (C.val.otherValue i) := by
    by_contra hcop
    obtain ⟨p, hpPrime, hpg, hpD⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpgMem : p ∈ g.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpg, hgSq.ne_zero⟩
    exact hDrough p hpPrime (hgSupport p hpgMem).2 hpD
  have hMg : Nat.Coprime (CoverBPZ.refinementModulus S) g := by
    by_contra hcop
    obtain ⟨p, hpPrime, hpM, hpg⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpSmall := CoverBPZ.prime_lt_two_mul_k_of_dvd_refinementModulus
      S hpPrime hpM
    have hpgMem : p ∈ g.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpg, hgSq.ne_zero⟩
    have hpLarge : 2 * S.k ≤ p :=
      (le_max_left (2 * S.k) 3).trans (hgSupport p hpgMem).1
    omega
  exact ⟨hDrough, hDsq, hgD, hMD, hMg.symm.mul_right hgD,
    (Nat.squarefree_mul hgD).2 ⟨hgSq, hDsq⟩, hMg.mul_right hMD⟩

/-- After `g=u*v`, the actual squarefree factor `D*v` has every hypothesis
needed by the fixed-factor Kloosterman theorem, while `u` is a unit modulo
it. -/
theorem certificate_split_applicability
    {B K X z medium large g u v : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hC : C ∈ MediumCertificateCover.certificates S X z medium large i)
    (hz : 2 * S.k ≤ z) (hgSq : Squarefree g) (hguv : g = u * v)
    (hgSupport : ∀ p ∈ g.primeFactors,
      max (2 * S.k) 3 ≤ p ∧ p < z) :
    let D := C.val.otherValue i
    Squarefree (D * v) ∧
      Nat.Coprime (CoverBPZ.refinementModulus S) (D * v) ∧
      Nat.Coprime u (D * v) ∧
      (∀ p ∈ (D * v).primeFactors, 2 < p) := by
  dsimp only
  obtain ⟨hDrough,hDsq,hgD,hMD,_hgMD,hgDsq,hMgD⟩ :=
    certificate_sieve_complement_applicability hC hgSq hgSupport
  subst g
  have huv : Nat.Coprime u v := Nat.coprime_of_squarefree_mul hgSq
  have huD : Nat.Coprime u (C.val.otherValue i) :=
    Nat.Coprime.of_dvd_left (dvd_mul_right u v) hgD
  have hvD : Nat.Coprime v (C.val.otherValue i) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left v u) hgD
  have hvSq : Squarefree v := hgSq.of_mul_right
  have hMuv : Nat.Coprime (CoverBPZ.refinementModulus S) (u * v) :=
    Nat.Coprime.of_dvd_right (dvd_mul_right (u * v) (C.val.otherValue i)) hMgD
  have hMv : Nat.Coprime (CoverBPZ.refinementModulus S) v :=
    Nat.Coprime.of_dvd_right (dvd_mul_left v u) hMuv
  refine ⟨(Nat.squarefree_mul hvD.symm).2 ⟨hDsq,hvSq⟩,
    hMD.mul_right hMv, huD.mul_right huv, ?_⟩
  intro p hpMem
  have hpPrime := Nat.prime_of_mem_primeFactors hpMem
  rcases hpPrime.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hpMem) with hpD | hpv
  · have hpLower : z ≤ p := by
      by_contra hpz
      exact hDrough p hpPrime (by omega) hpD
    have hk3 := S.hk3
    omega
  · have hpvMem : p ∈ v.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hpPrime,hpv,hvSq.ne_zero⟩
    have hpgMem : p ∈ (u * v).primeFactors := Nat.mem_primeFactors.mpr
      ⟨hpPrime,hpv.trans (dvd_mul_left v u),hgSq.ne_zero⟩
    have hpThree : 3 ≤ p :=
      (le_max_right (2 * S.k) 3).trans (hgSupport p hpgMem).1
    omega

/-- Congruence of a combined fixed residue to the tuple's complementary
residue. -/
theorem combinedResidue_mod_otherValue
    {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (v a : ℕ)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) v) :
    MediumComplementFourier.combinedResidue C i v a hcop ≡
      C.val.otherResidue i [MOD C.val.otherValue i] := by
  exact ((simultaneousResidue_mod_left hcop _ _).of_dvd
    (dvd_mul_left (C.val.otherValue i) (CoverBPZ.refinementModulus S))).trans
      (simultaneousResidue_mod_right
        (MediumComplementFourier.fixed_complement_coprime C i) _ _)

/-- The combined residue cannot collide with the removed index modulo any
prime of the rough complementary product. -/
theorem gcd_combinedResidue_sub_index_eq_one
    {B K X z medium large v a : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X}
    (hC : C ∈ MediumCertificateCover.certificates S X z medium large i)
    (hkz : S.k ≤ z)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) v) :
    Int.gcd
      ((MediumComplementFourier.combinedResidue C i v a hcop : ℤ) - i.val)
      (C.val.otherValue i : ℤ) = 1 := by
  let gamma := MediumComplementFourier.combinedResidue C i v a hcop
  have hrough := certificate_otherValue_rough hC
  have hgamma := combinedResidue_mod_otherValue C i v a hcop
  apply CoverBPZ.int_gcd_eq_one_of_no_prime_common
  intro p hp hpDiff hpD
  have hpDNat : p ∣ C.val.otherValue i := by exact_mod_cast hpD
  have hpLower : z ≤ p := by
    by_contra hpz
    exact hrough p hp (by omega) hpDNat
  have hgammaI : gamma ≡ i.val [MOD p] := by
    rw [Nat.modEq_iff_dvd]
    have hneg : (p : ℤ) ∣ -((gamma : ℤ) - i.val) := dvd_neg.mpr hpDiff
    simpa only [neg_sub] using hneg
  have hgammaOther : gamma ≡ C.val.otherResidue i [MOD p] :=
    hgamma.of_dvd hpDNat
  have hotherI : C.val.otherResidue i ≡ i.val [MOD p] :=
    hgammaOther.symm.trans hgammaI
  unfold TupleCertificate.otherValue at hpDNat
  obtain ⟨j,hj,hpj⟩ := (hp.prime.dvd_finsetProd_iff C.val.factor).mp hpDNat
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hotherJ : C.val.otherResidue i ≡ j.val [MOD p] :=
    (C.val.otherResidue_mod_factor hji).of_dvd hpj
  have hij : i.val ≡ j.val [MOD p] := hotherI.symm.trans hotherJ
  exact hji (Fin.ext (hij.eq_of_lt_of_lt
    (i.isLt.trans_le (hkz.trans hpLower))
    (j.isLt.trans_le (hkz.trans hpLower))).symm)

/-- Source-facing CRT reciprocity with the fixed modulus written as
`Q = M*D*v` and the varying factor written as `u*t`.  The first character
contains the canonical inverse of `u*t` modulo `Q`; the second is the small
full-modulus phase at the distinguished residue. -/
theorem stdAddChar_medium_reciprocity
    (M D v u t gamma i : ℕ)
    [NeZero (M * D * v)] [NeZero (u * t)]
    (hcop : Nat.Coprime (M * D * v) (u * t))
    (h : ZMod ((M * D * v) * (u * t))) :
    ZMod.stdAddChar
        (h * (simultaneousResidue hcop gamma i :
          ZMod ((M * D * v) * (u * t)))) =
      ZMod.stdAddChar
          ((ZMod.chineseRemainder hcop h).1 *
            ((gamma : ZMod (M * D * v)) - (i : ZMod (M * D * v))) *
            (Nat.gcdB (M * D * v) (u * t) : ZMod (M * D * v))) *
        ZMod.stdAddChar
          (h * (i : ZMod ((M * D * v) * (u * t)))) := by
  exact SimultaneousFourier.stdAddChar_mul_simultaneousResidue_reciprocity
    hcop gamma i h

/-- Multiplying a residue by a unit cannot add a common divisor with the
modulus.  The divisibility form is convenient because it composes through
the inverse and Bézout twists in the Kloosterman coefficient. -/
theorem gcd_val_mul_unit_dvd_left
    (q : ℕ) [NeZero q] (a w : ZMod q) (hw : IsUnit w) :
    Nat.gcd (a * w).val q ∣ Nat.gcd a.val q := by
  obtain ⟨w', rfl⟩ := hw
  have hwcop : Nat.Coprime (w' : ZMod q).val q :=
    ZMod.val_coe_unit_coprime w'
  have hmod : Nat.ModEq q (a * (w' : ZMod q)).val
      (a.val * (w' : ZMod q).val) := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  rw [hmod.gcd_eq]
  apply Nat.dvd_gcd
  · have hGq : Nat.gcd (a.val * (w' : ZMod q).val) q ∣ q :=
      Nat.gcd_dvd_right _ _
    have hcopG : Nat.Coprime
        (Nat.gcd (a.val * (w' : ZMod q).val) q) (w' : ZMod q).val :=
      (hwcop.of_dvd_right hGq).symm
    exact hcopG.dvd_of_dvd_mul_right (Nat.gcd_dvd_left _ _)
  · exact Nat.gcd_dvd_right _ _

/-- The gcd of an integer residue representative with the modulus is the
ordinary integer gcd. -/
theorem gcd_val_intCast (q : ℕ) [NeZero q] (a : ℤ) :
    Nat.gcd (a : ZMod q).val q = Int.gcd a q := by
  rw [← Int.gcd_natCast_natCast, ZMod.val_intCast, Int.gcd_emod]

/-- If `delta` is coprime to `D`, its product with a nonzero frequency can
contribute to the `D`-part of the local gcd only through that frequency. -/
theorem gcd_frequency_mul_difference_le
    (D : ℕ) (h delta : ℤ) (hh : h ≠ 0)
    (hdelta : Int.gcd delta D = 1) :
    Int.gcd (h * delta) D ≤ h.natAbs := by
  change Nat.gcd ((h * delta).natAbs) D ≤ h.natAbs
  rw [Int.natAbs_mul]
  have hcop : Nat.Coprime delta.natAbs D := by
    rwa [Nat.coprime_iff_gcd_eq_one]
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hh)
  have hGd : Nat.gcd (h.natAbs * delta.natAbs) D ∣ D :=
    Nat.gcd_dvd_right _ _
  have hcopG : Nat.Coprime
      (Nat.gcd (h.natAbs * delta.natAbs) D) delta.natAbs :=
    (hcop.of_dvd_right hGd).symm
  exact hcopG.dvd_of_dvd_mul_right (Nat.gcd_dvd_left _ _)

/-- Splitting the squarefree modulus as `D*v` costs at most the full factor
`v` beyond the gcd already present on `D`. -/
theorem gcd_mul_right_le
    (D v x : ℕ) (hD : 0 < D) (hv : 0 < v) :
    Nat.gcd x (D * v) ≤ v * Nat.gcd x D := by
  have hdiv : Nat.gcd x (D * v) ∣ Nat.gcd x D * v :=
    (gcd_mul_dvd_mul_gcd x D v).trans
      (Nat.mul_dvd_mul_left (Nat.gcd x D) (Nat.gcd_dvd_right x v))
  have hpos : 0 < v * Nat.gcd x D :=
    Nat.mul_pos hv (Nat.gcd_pos_of_pos_right x hD)
  exact Nat.le_of_dvd hpos (by simpa [Nat.mul_comm] using hdiv)

/-- The local inverse coefficient before the fixed-factor CRT twist. -/
noncomputable def inverseCoefficient
    (q u : ℕ) (h delta : ℤ) : ZMod q :=
  (h * delta : ZMod q) * (u : ZMod q)⁻¹

/-- The exact coefficient whose gcd occurs in the fixed-factor squarefree
Kloosterman theorem. -/
noncomputable def localKloostermanCoefficient
    (M q u : ℕ) (h delta : ℤ) : ZMod q :=
  inverseCoefficient q u h delta * (Nat.gcdA M q : ZMod q)

set_option linter.style.haveILetI false in
/-- Both inverse twists are units.  Cancellation on `D` therefore gives
the source-required crude loss `v*|h|`; no coprimality with `v` is used. -/
theorem gcd_localKloostermanCoefficient_le
    (M D v u : ℕ) [NeZero (D * v)]
    (h delta : ℤ) (hD : 0 < D) (hh : h ≠ 0)
    (hdelta : Int.gcd delta D = 1)
    (hu : Nat.Coprime u (D * v))
    (hM : Nat.Coprime M (D * v)) :
    Nat.gcd (localKloostermanCoefficient M (D * v) u h delta).val (D * v) ≤
      v * h.natAbs := by
  have huUnit : IsUnit (u : ZMod (D * v)) :=
    (ZMod.isUnit_iff_coprime u (D * v)).2 hu
  have huInv : IsUnit (u : ZMod (D * v))⁻¹ := by
    have huInt : IsUnit (((u : ℤ) : ZMod (D * v))) := by
      simpa only [Int.cast_natCast] using huUnit
    simpa only [Int.cast_natCast] using ZMod.isUnit_inv huInt
  have hAUnit : IsUnit (Nat.gcdA M (D * v) : ZMod (D * v)) :=
    Kloosterman.isUnit_gcdA M (D * v) hM
  have htwist : Nat.gcd
      (localKloostermanCoefficient M (D * v) u h delta).val (D * v) ∣
      Nat.gcd (h * delta : ZMod (D * v)).val (D * v) := by
    exact (gcd_val_mul_unit_dvd_left (D * v)
      (inverseCoefficient (D * v) u h delta)
      (Nat.gcdA M (D * v) : ZMod (D * v)) hAUnit).trans
        (gcd_val_mul_unit_dvd_left (D * v)
          (h * delta : ZMod (D * v)) (u : ZMod (D * v))⁻¹ huInv)
  have hDdvd : D ∣ D * v := dvd_mul_right D v
  haveI : NeZero D := ⟨hD.ne'⟩
  have hmodD : Nat.ModEq D (h * delta : ZMod (D * v)).val
      (h * delta : ZMod D).val := by
    rw [← ZMod.natCast_eq_natCast_iff]
    calc
      ((h * delta : ZMod (D * v)).val : ZMod D) =
          ZMod.castHom hDdvd (ZMod D)
            ((h * delta : ZMod (D * v)).val : ZMod (D * v)) := by
        simp only [map_natCast]
      _ = ZMod.castHom hDdvd (ZMod D) (h * delta : ZMod (D * v)) := by
        rw [ZMod.natCast_zmod_val]
      _ = (h * delta : ZMod D) := by
        simp only [map_mul, map_intCast]
      _ = ((h * delta : ZMod D).val : ZMod D) :=
        (ZMod.natCast_zmod_val (h * delta : ZMod D)).symm
  have hbaseD : Nat.gcd (h * delta : ZMod (D * v)).val D =
      Int.gcd (h * delta) D := by
    rw [hmodD.gcd_eq]
    simpa only [Int.cast_mul] using gcd_val_intCast D (h * delta)
  have hv0 : v ≠ 0 := by
    intro hv
    apply NeZero.ne (D * v)
    simp [hv]
  have hv : 0 < v := Nat.pos_of_ne_zero hv0
  calc
    Nat.gcd (localKloostermanCoefficient M (D * v) u h delta).val (D * v) ≤
        Nat.gcd (h * delta : ZMod (D * v)).val (D * v) :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (Nat.mul_pos hD hv)) htwist
    _ ≤ v * Nat.gcd (h * delta : ZMod (D * v)).val D :=
      gcd_mul_right_le D v _ hD hv
    _ = v * Int.gcd (h * delta) D := by rw [hbaseD]
    _ ≤ v * h.natAbs := Nat.mul_le_mul_left v
      (gcd_frequency_mul_difference_le D h delta hh hdelta)

/-- A full coefficient with arbitrary fixed-modulus coordinate and the
prescribed inverse coefficient on the squarefree coordinate. -/
noncomputable def fullCoefficient
    (M q u : ℕ) (hcop : Nat.Coprime M q)
    (fixed : ZMod M) (h delta : ℤ) : ZMod (M * q) :=
  (ZMod.chineseRemainder hcop).symm
    (fixed, inverseCoefficient q u h delta)

theorem fullCoefficient_squarefree_coordinate
    (M q u : ℕ) (hcop : Nat.Coprime M q)
    (fixed : ZMod M) (h delta : ℤ) :
    (ZMod.chineseRemainder hcop
        (fullCoefficient M q u hcop fixed h delta)).2 =
      inverseCoefficient q u h delta := by
  simp [fullCoefficient]

/-- Arbitrary-interval Kloosterman estimate with the local gcd replaced by
the certificate-derived loss `v*|h|`. -/
theorem norm_incompleteInterval_medium
    (M D v u : ℕ) [NeZero M] [NeZero (D * v)]
    (hcop : Nat.Coprime M (D * v))
    (hsq : Squarefree (D * v))
    (hlarge : ∀ p ∈ (D * v).primeFactors, 2 < p)
    (fixed : ZMod M) (h delta : ℤ)
    (hD : 0 < D) (hh : h ≠ 0)
    (hdelta : Int.gcd delta D = 1)
    (hu : Nat.Coprime u (D * v))
    (A : ℤ) (L : ℕ) :
    ‖Kloosterman.incompleteInterval (M * (D * v))
        (fullCoefficient M (D * v) u hcop fixed h delta) A L‖ ≤
      ((L / (M * (D * v)) + 1 : ℕ) : ℝ) *
        ((Real.log (M * (D * v) : ℕ) + 1) *
          ((4 : ℝ) ^ (D * v).primeFactors.card *
            Real.sqrt (D * v : ℝ) * Real.sqrt (v * h.natAbs : ℝ) * M)) := by
  have hraw :=
    Erdos387Proof.PeriodicCompletion.Kloosterman.norm_incompleteInterval_fixed_mul_squarefree_arbitrary
      M (D * v) hcop hsq hlarge
      (fullCoefficient M (D * v) u hcop fixed h delta) A L
  have hcoord :
      ((ZMod.chineseRemainder hcop
          (fullCoefficient M (D * v) u hcop fixed h delta)).2 *
        (Nat.gcdA M (D * v) : ZMod (D * v))) =
        localKloostermanCoefficient M (D * v) u h delta := by
    rw [fullCoefficient_squarefree_coordinate]
    rfl
  unfold Erdos387Proof.PeriodicCompletion.Kloosterman.fixedMulSquarefreeIntervalBound at hraw
  rw [hcoord] at hraw
  have hgcdR :
      ((Nat.gcd (localKloostermanCoefficient M (D * v) u h delta).val
        (D * v) : ℕ) : ℝ) ≤ (v * h.natAbs : ℕ) := by
    exact_mod_cast gcd_localKloostermanCoefficient_le
      M D v u h delta hD hh hdelta hu hcop
  have hmodulusOne : (1 : ℝ) ≤ (M * (D * v) : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (M * (D * v))))
  have hlog : 0 ≤ Real.log (M * (D * v) : ℕ) + 1 :=
    add_nonneg (Real.log_nonneg hmodulusOne) zero_le_one
  apply hraw.trans
  simp only [Nat.cast_mul]
  gcongr
  · simpa only [Nat.cast_mul] using hlog
  · simpa only [Nat.cast_mul] using hgcdR

end Erdos387Proof.MediumReciprocalPhase
