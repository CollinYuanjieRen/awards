import Erdos387Proof.MediumPartialFourier
import Erdos387Proof.MediumWeightedPhase
import Erdos387Proof.GcdFactorReindex
import Erdos387Proof.MediumFourierTailDecay

/-!
# Exact Fourier blocks in one medium complementary fibre

This file keeps the sum over the entire varying-factor interval inside the
complex norm.  The interval is first split by the actual gcd with the sieve
product.  Within one gcd stratum the varying factor is `u*t`; the remaining
coprimality condition is represented by the zero extension in
`maskedFourierSummand`.
-/

set_option autoImplicit false

namespace Erdos387Proof.MediumFibreFourier

open Erdos387 IntegerClassFourier IntegerSieveResidues
open MediumCertificateCover MediumComplementFourier MediumFactorWindow
open MediumFourierReduction MediumPartialFourier MediumWeightedPhase
open scoped BigOperators

/-- Reassociating the actual certificate CRT and the sieve CRT gives the
complement-first residue used by the reciprocal-phase calculation. -/
theorem certificateResidue_eq_complementResidue
    {B K X v : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (a : ℕ)
    [NeZero v] (ha : a < v)
    (hDv : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) v)
    (hfull : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v)
    (hvd : Nat.Coprime v (C.val.factor i))
    (hcombined : Nat.Coprime
      (CoverBPZ.refinementModulus S * C.val.otherValue i * v)
        (C.val.factor i)) :
    simultaneousResidue hfull
        (simultaneousResidue C.property
          (CoverBPZ.refinementResidue S) C.val.crtResidue) a =
      simultaneousResidue hcombined
        (combinedResidue C i v a hDv) i.val := by
  let left := simultaneousResidue hfull
    (simultaneousResidue C.property
      (CoverBPZ.refinementResidue S) C.val.crtResidue) a
  let right := simultaneousResidue hcombined
    (combinedResidue C i v a hDv) i.val
  have hleftClass : MediumSieveSmoothing.integerClass C (left : ℤ) := by
    rw [IntegerClassFourier.integerClass_iff_combined]
    exact Int.natCast_modEq_iff.mpr
      (simultaneousResidue_mod_left hfull _ _)
  have hleftV : (((left : ℤ) % (v : ℤ)).toNat = a) := by
    rw [IntegerClassFourier.natResidue_eq_iff_modEq (left : ℤ)
      (NeZero.pos v) ha]
    exact Int.natCast_modEq_iff.mpr
      (simultaneousResidue_mod_right hfull _ _)
  have hmodInt₀ := (integerClass_and_residue_iff C i v a
    (NeZero.pos v) ha hDv hvd (left : ℤ)).mp ⟨hleftClass, hleftV⟩
  have hmodInt : Int.ModEq
      ((CoverBPZ.refinementModulus S * C.val.otherValue i * v) *
        C.val.factor i : ℕ) (left : ℤ) (right : ℤ) := by
    simpa only [right] using hmodInt₀
  have hmod : left ≡ right
      [MOD (CoverBPZ.refinementModulus S * C.val.otherValue i * v) *
        C.val.factor i] := by
    exact_mod_cast hmodInt
  have hmodulus :
      CoverBPZ.refinementModulus S * C.val.value * v =
        (CoverBPZ.refinementModulus S * C.val.otherValue i * v) *
          C.val.factor i := by
    rw [← C.val.factor_mul_otherValue i]
    ring
  have hleftLt : left <
      (CoverBPZ.refinementModulus S * C.val.otherValue i * v) *
        C.val.factor i := by
    rw [← hmodulus]
    exact simultaneousResidue_lt hfull
      (Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos)
      (NeZero.pos v) _ _
  have hrightLt : right <
      (CoverBPZ.refinementModulus S * C.val.otherValue i * v) *
        C.val.factor i := by
    exact simultaneousResidue_lt hcombined
      (Nat.mul_pos
        (Nat.mul_pos (CoverBPZ.refinementModulus_pos S)
          (C.val.otherValue_pos i)) (NeZero.pos v))
      (C.val.positive i) _ _
  exact hmod.eq_of_lt_of_lt hleftLt hrightLt

/-- A Fourier term is invariant under simultaneous identification of its
modulus and natural residue.  Isolating the dependent transport here keeps
the certificate proof independent of typeclass proof terms. -/
theorem fourierTerm_eq_of_modulus_eq
    (X q₁ q₂ r₁ r₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (h : ℤ) (hq : q₁ = q₂) (hr : r₁ = r₂) :
    (ZMod.stdAddChar (-(h : ZMod q₁) * (r₁ : ZMod q₁)) *
      TentFourier.coefficient X q₁ (h : ZMod q₁)).re =
    (ZMod.stdAddChar (-(h : ZMod q₂) * (r₂ : ZMod q₂)) *
      TentFourier.coefficient X q₂ (h : ZMod q₂)).re := by
  subst q₂
  subst r₂
  rfl

/-- Proof arguments and a propositionally equal residual modulus do not
change the explicit finite nonzero partial sum. -/
theorem certificateNonzeroPartial_congr
    {B K X H v₁ v₂ : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) [NeZero v₁] [NeZero v₂]
    (h₁ : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v₁)
    (h₂ : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v₂)
    (hv : v₁ = v₂) :
    certificateNonzeroPartial C v₁ H h₁ =
      certificateNonzeroPartial C v₂ H h₂ := by
  subst v₂
  rfl

/-- Canonical natural CRT residues transport across equal factor moduli. -/
theorem simultaneousResidue_congr
    {M₁ M₂ d₁ d₂ : ℕ}
    (h₁ : Nat.Coprime M₁ d₁) (h₂ : Nat.Coprime M₂ d₂)
    (a b : ℕ) (hM : M₁ = M₂) (hd : d₁ = d₂) :
    simultaneousResidue h₁ a b = simultaneousResidue h₂ a b := by
  subst M₂
  subst d₂
  rfl

set_option linter.style.haveILetI false in
/-- For a factor written as `u*t`, the explicit nonzero Fourier sum of one
certificate is the proof-carrying masked summand.  This is an equality,
before any triangle inequality or analytic estimate. -/
theorem certificateNonzeroPartial_eq_masked
    {B K X v u t H : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k)
    [NeZero v] [NeZero u] [NeZero t]
    [NeZero (CoverBPZ.refinementModulus S * (C.val.otherValue i * v))]
    (hfactor : C.val.factor i = u * t)
    (hv : Squarefree v)
    (hDv : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) v)
    (hfull : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v)
    (huQ : Nat.Coprime u
      (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)))
    (htQ : Nat.Coprime t
      (CoverBPZ.refinementModulus S * (C.val.otherValue i * v))) :
    certificateNonzeroPartial C v H hfull =
      ∑ a ∈ localAssignmentResidues v S.k,
        ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
          (maskedFourierSummand X
            (CoverBPZ.refinementModulus S * (C.val.otherValue i * v))
            u (combinedResidue C i v a hDv) i.val huQ h t
              (NeZero.pos t)).re := by
  classical
  have hvQ : v ∣ CoverBPZ.refinementModulus S * (C.val.otherValue i * v) := by
    use CoverBPZ.refinementModulus S * C.val.otherValue i
    ring
  have hvd : Nat.Coprime v (C.val.factor i) := by
    rw [hfactor]
    exact (Nat.coprime_mul_iff_left.mpr
      ⟨huQ.of_dvd_right hvQ, htQ.of_dvd_right hvQ⟩).symm
  have hmodulus :
      CoverBPZ.refinementModulus S * C.val.value * v =
        (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) * (u * t) := by
    rw [← C.val.factor_mul_otherValue i, hfactor]
    ring
  unfold certificateNonzeroPartial nonzeroPartial
  apply Finset.sum_congr rfl
  intro a ha
  have haLt :=
    (ConstrainedSieveResidues.mem_localAssignmentResidues_iff hv).mp ha |>.1
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hcopUT : Nat.Coprime
      (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) (u * t) :=
    huQ.symm.mul_right htQ.symm
  have hcombined : Nat.Coprime
      (CoverBPZ.refinementModulus S * C.val.otherValue i * v)
        (C.val.factor i) := by
    rw [hfactor]
    simpa only [Nat.mul_assoc] using hcopUT
  have hres₀ := certificateResidue_eq_complementResidue
    C i a haLt hDv hfull hvd hcombined
  have hres :
      simultaneousResidue hfull
          (simultaneousResidue C.property
            (CoverBPZ.refinementResidue S) C.val.crtResidue) a =
        simultaneousResidue hcopUT (combinedResidue C i v a hDv) i.val :=
    hres₀.trans (simultaneousResidue_congr hcombined hcopUT
      (combinedResidue C i v a hDv) i.val (by simp only [Nat.mul_assoc]) hfactor)
  letI : NeZero (CoverBPZ.refinementModulus S * C.val.value * v) :=
    ⟨(Nat.mul_pos
      (Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos)
      (NeZero.pos v)).ne'⟩
  rw [maskedFourierSummand]
  simp only [dif_pos htQ]
  exact fourierTerm_eq_of_modulus_eq X _ _ _ _ h hmodulus hres

/-- Total version of the proof-carrying summand.  The zero value at `t=0`
is only for convenient finite-set reindexing; all actual interval elements
are positive. -/
noncomputable def totalMaskedFourierSummand
    (X Q u gamma i : ℕ) [NeZero Q] [NeZero u]
    (huQ : Nat.Coprime u Q) (h : ℤ) (t : ℕ) : ℂ := by
  by_cases ht : 0 < t
  · exact maskedFourierSummand X Q u gamma i huQ h t ht
  · exact 0

theorem totalMaskedFourierSummand_of_pos
    (X Q u gamma i : ℕ) [NeZero Q] [NeZero u]
    (huQ : Nat.Coprime u Q) (h : ℤ) (t : ℕ) (ht : 0 < t) :
    totalMaskedFourierSummand X Q u gamma i huQ h t =
      maskedFourierSummand X Q u gamma i huQ h t ht := by
  rw [totalMaskedFourierSummand]
  simp only [dif_pos ht]

/-- The proof-carrying masked term transports across equal moduli and equal
natural phase residues. -/
theorem maskedFourierSummand_congr
    (X q₁ q₂ u gamma₁ gamma₂ i : ℕ)
    [NeZero q₁] [NeZero q₂] [NeZero u]
    (hu₁ : Nat.Coprime u q₁) (hu₂ : Nat.Coprime u q₂)
    (h : ℤ) (t : ℕ) (ht : 0 < t)
    (hq : q₁ = q₂) (hgamma : gamma₁ = gamma₂) :
    maskedFourierSummand X q₁ u gamma₁ i hu₁ h t ht =
      maskedFourierSummand X q₂ u gamma₂ i hu₂ h t ht := by
  subst q₂
  subst gamma₂
  rfl

/-- A natural half-open interval is a translated range. -/
theorem sum_Ioc_eq_sum_range {R : Type*} [AddCommMonoid R]
    (A B : ℕ) (F : ℕ → R) :
    (∑ t ∈ Finset.Ioc A B, F t) =
      ∑ r ∈ Finset.range (B - A), F (A + r + 1) := by
  classical
  apply Finset.sum_bij (fun t _ => t - A - 1)
  · intro t ht
    simp only [Finset.mem_range]
    have h := Finset.mem_Ioc.mp ht
    omega
  · intro a ha b hb hab
    have haa := Finset.mem_Ioc.mp ha
    have hbb := Finset.mem_Ioc.mp hb
    omega
  · intro r hr
    refine ⟨A + r + 1, Finset.mem_Ioc.mpr ?_, ?_⟩
    · have := Finset.mem_range.mp hr
      omega
    · omega
  · intro t ht
    have h := Finset.mem_Ioc.mp ht
    congr 1
    omega

/-- The coprimality filter can be removed because the masked summand is
zero on its complement; the result is the consecutive range consumed by
the weighted incomplete-sum theorem. -/
theorem sum_interval_totalMasked_eq_range
    (A B X Q u gamma i : ℕ) [NeZero Q] [NeZero u]
    (huQ : Nat.Coprime u Q) (h : ℤ) :
    (∑ t ∈ GcdFactorReindex.interval A B Q,
      totalMaskedFourierSummand X Q u gamma i huQ h t) =
      ∑ r ∈ Finset.range (B - A),
        maskedFourierSummand X Q u gamma i huQ h (A + r + 1)
          (by omega) := by
  classical
  rw [show GcdFactorReindex.interval A B Q =
      (Finset.Ioc A B).filter (fun t => Nat.Coprime t Q) by rfl]
  rw [Finset.sum_filter]
  have hremove :
      (∑ t ∈ Finset.Ioc A B,
        if Nat.Coprime t Q then
          totalMaskedFourierSummand X Q u gamma i huQ h t else 0) =
      ∑ t ∈ Finset.Ioc A B,
        totalMaskedFourierSummand X Q u gamma i huQ h t := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases htQ : Nat.Coprime t Q
    · simp only [if_pos htQ]
    · have htpos : 0 < t := (Nat.zero_le A).trans_lt (Finset.mem_Ioc.mp ht).1
      rw [if_neg htQ, totalMaskedFourierSummand_of_pos _ _ _ _ _ _ _ _ htpos]
      rw [maskedFourierSummand]
      simp only [dif_neg htQ]
  rw [hremove, sum_Ioc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  exact totalMaskedFourierSummand_of_pos X Q u gamma i huQ h
    (A + r + 1) (by omega)

/-- Total actual nonzero partial sum, with the same domain guards as
`windowCertificatePartial`. -/
noncomputable def windowCertificateNonzeroPartial
    {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (i : Fin S.k) (C : RefinedTupleCertificate S X)
    (z medium large H : ℕ) (T : Finset ℕ) : ℝ := by
  classical
  exact if hC : C ∈ certificates S X z medium large i then
    if hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset then
      let g := ∏ p ∈ T, p
      have hg : Squarefree g := MediumSignedMainTerm.primeSubsetProduct_squarefree
        (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
        (Finset.mem_powerset.mp hT)
      letI : NeZero (g / Nat.gcd g (C.val.factor i)) :=
        ⟨MediumFourierTail.gcdQuotient_pos
          (Nat.pos_of_ne_zero hg.ne_zero) |>.ne'⟩
      certificateNonzeroPartial C (g / Nat.gcd g (C.val.factor i)) H
        (MediumCertificateZeroMode.gcd_quotient_coprime_classModulus C i hg
          (MediumComplementBounds.window_product_coprime_complement hC hT).symm)
    else 0
  else 0

set_option linter.style.haveILetI false in
/-- The arithmetic window condition turns the retained partial remainder
into the explicit nonzero integer-frequency sum. -/
theorem partialRemainder_eq_windowCertificateNonzeroPartial
    {B K X z medium large H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X} {T : Finset ℕ}
    (hB : 0 < B) (hX : 0 < X) (hHX : 4 * B * H ≤ X)
    (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset) :
    partialRemainder C i z medium large H T =
      windowCertificateNonzeroPartial i C z medium large H T := by
  classical
  let g := ∏ p ∈ T, p
  have hg : Squarefree g := MediumSignedMainTerm.primeSubsetProduct_squarefree
    (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
    (Finset.mem_powerset.mp hT)
  let v := g / Nat.gcd g (C.val.factor i)
  have hv : 0 < v := MediumFourierTail.gcdQuotient_pos
    (Nat.pos_of_ne_zero hg.ne_zero)
  letI : NeZero v := ⟨hv.ne'⟩
  have hcop := (MediumComplementBounds.window_product_coprime_complement hC hT).symm
  have hHq : 2 * H < CoverBPZ.refinementModulus S * C.val.value * v :=
    MediumFourierTailDecay.two_mul_height_lt_modulus hB
      (CoverBPZ.refinementModulus_pos S) hv
      (Finset.mem_filter.mp hC).2.2.1 hHX
  unfold partialRemainder MediumFourierTail.windowCertificatePartial
    windowCertificateNonzeroPartial
  simp only [dif_pos hC, dif_pos hT]
  exact MediumPartialFourier.certificatePartial_sub_zeroCoefficient C i hX hg
    hcop (fun (p : ℕ) (hp : p ∈ g.primeFactors) => by
      have hprime : ∀ q ∈ T, q.Prime := fun q hq =>
        (MediumSieveEuler.mem_windowPrimes.mp
          (Finset.mem_powerset.mp hT hq)).1
      rw [Nat.primeFactors_prod hprime] at hp
      have hk3 := S.hk3
      have hp4 := (MediumSieveEuler.mem_windowPrimes.mp
        (Finset.mem_powerset.mp hT hp)).2.1
      omega) hHq

/-- The full varying-factor sum is still intact when every retained partial
remainder is replaced by its explicit nonzero Fourier sum. -/
theorem sum_partialRemainder_eq_sum_windowCertificateNonzeroPartial
    {B K X z medium large H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X} {T : Finset ℕ}
    (hB : 0 < B) (hX : 0 < X) (hHX : 4 * B * H ≤ X)
    (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset) :
    (∑ d ∈ factors B X (C.val.otherValue i)
        (CoverBPZ.refinementModulus S) medium large,
      partialRemainder (fromFactor C i medium large d) i
        z medium large H T) =
      ∑ d ∈ factors B X (C.val.otherValue i)
          (CoverBPZ.refinementModulus S) medium large,
        windowCertificateNonzeroPartial i
          (fromFactor C i medium large d) z medium large H T := by
  classical
  apply Finset.sum_congr rfl
  intro d hd
  have hE := fromFactor_mem_fibre C i hB
    (Finset.mem_filter.mp hC).2.2.2.2.2 hd
  exact partialRemainder_eq_windowCertificateNonzeroPartial
    hB hX hHX (Finset.mem_filter.mp hE).1 hT

/-- Exact gcd stratification and division of the varying-factor interval.
No absolute value has yet been taken. -/
theorem sum_windowCertificateNonzeroPartial_eq_gcdIntervals
    {B K X z medium large H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X} {T : Finset ℕ}
    (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset) :
    let g := ∏ p ∈ T, p
    (∑ d ∈ factors B X (C.val.otherValue i)
        (CoverBPZ.refinementModulus S) medium large,
      windowCertificateNonzeroPartial i
        (fromFactor C i medium large d) z medium large H T) =
      ∑ u ∈ g.divisors,
        ∑ t ∈ GcdFactorReindex.interval
          (lower B X (C.val.otherValue i) medium / u)
          (upper X (C.val.otherValue i) large / u)
          (CoverBPZ.refinementModulus S * (C.val.otherValue i * (g / u))),
          windowCertificateNonzeroPartial i
            (fromFactor C i medium large (u * t)) z medium large H T := by
  classical
  dsimp only
  let g := ∏ p ∈ T, p
  have hg : 0 < g := by
    apply Finset.prod_pos
    intro p hp
    exact (MediumSieveEuler.mem_windowPrimes.mp
      (Finset.mem_powerset.mp hT hp)).1.pos
  have hcop : Nat.Coprime g
      (CoverBPZ.refinementModulus S * C.val.otherValue i) :=
    MediumComplementBounds.window_product_coprime_complement hC hT
  change (∑ d ∈ GcdFactorReindex.interval
      (lower B X (C.val.otherValue i) medium)
      (upper X (C.val.otherValue i) large)
      (CoverBPZ.refinementModulus S * C.val.otherValue i),
      windowCertificateNonzeroPartial i
        (fromFactor C i medium large d) z medium large H T) = _
  rw [MediumZeroModeIdentity.sum_interval_eq_sum_gcd_fibres _ _ _ g hg]
  apply Finset.sum_congr rfl
  intro u hu
  have hudvd := Nat.dvd_of_mem_divisors hu
  have hu : 0 < u := Nat.pos_of_mem_divisors hu
  have huQ := hcop.of_dvd_left hudvd
  have hguv : u * (g / u) = g := Nat.mul_div_cancel' hudvd
  have hfilter :
      (GcdFactorReindex.interval
          (lower B X (C.val.otherValue i) medium)
          (upper X (C.val.otherValue i) large)
          (CoverBPZ.refinementModulus S * C.val.otherValue i)).filter
          (fun d => Nat.gcd g d = u) =
      (GcdFactorReindex.interval
          (lower B X (C.val.otherValue i) medium)
          (upper X (C.val.otherValue i) large)
          (CoverBPZ.refinementModulus S * C.val.otherValue i)).filter
          (fun d => Nat.gcd (u * (g / u)) d = u) := by
    rw [hguv]
  rw [hfilter]
  simpa only [Nat.mul_assoc] using
    GcdFactorReindex.sum_filter_gcd_eq hu huQ _

set_option linter.style.haveILetI false in
/-- On one divided gcd fibre, the actual nonzero partial is the masked
reciprocal-phase summand with a residue independent of `t`. -/
theorem windowCertificateNonzeroPartial_fromFactor_mul_eq_masked
    {B K X z medium large H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X} {T : Finset ℕ}
    (hB : 0 < B)
    (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset)
    {u : ℕ} (huMem : u ∈ (∏ p ∈ T, p).divisors)
    {t : ℕ}
    (ht : t ∈ GcdFactorReindex.interval
      (lower B X (C.val.otherValue i) medium / u)
      (upper X (C.val.otherValue i) large / u)
      (CoverBPZ.refinementModulus S *
        (C.val.otherValue i * ((∏ p ∈ T, p) / u)))) :
    let g := ∏ p ∈ T, p
    let v := g / u
    let hDv : Nat.Coprime
        (CoverBPZ.refinementModulus S * C.val.otherValue i) v := by
      apply Nat.Coprime.of_dvd_right _
        (MediumComplementBounds.window_product_coprime_complement hC hT).symm
      exact Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors huMem)
    let _ : NeZero u := ⟨(Nat.pos_of_mem_divisors huMem).ne'⟩
    let _ : NeZero
        (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) :=
      ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S)
        (Nat.mul_pos (C.val.otherValue_pos i)
          (Nat.div_pos
            (Nat.le_of_dvd
              (Nat.pos_of_ne_zero
                (MediumSignedMainTerm.primeSubsetProduct_squarefree
                  (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
                  (Finset.mem_powerset.mp hT) |>.ne_zero))
              (Nat.dvd_of_mem_divisors huMem))
            (Nat.pos_of_mem_divisors huMem)))).ne'⟩
    windowCertificateNonzeroPartial i
        (fromFactor C i medium large (u * t)) z medium large H T =
      ∑ a ∈ localAssignmentResidues v S.k,
        ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
          (maskedFourierSummand X
            (CoverBPZ.refinementModulus S * (C.val.otherValue i * v))
            u (combinedResidue C i v a hDv) i.val
              (by
                have hgcop := MediumComplementBounds.window_product_coprime_complement hC hT
                have huv := Nat.coprime_of_squarefree_mul
                  (show Squarefree (u * v) by
                    rw [show u * v = g from Nat.mul_div_cancel'
                      (Nat.dvd_of_mem_divisors huMem)]
                    exact MediumSignedMainTerm.primeSubsetProduct_squarefree
                      (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
                      (Finset.mem_powerset.mp hT))
                have huMD := hgcop.of_dvd_left (Nat.dvd_of_mem_divisors huMem)
                simpa only [Nat.mul_assoc] using huMD.mul_right huv)
              h t (by
                exact (Nat.zero_le _).trans_lt
                  (Finset.mem_Ioc.mp (Finset.mem_filter.mp ht).1).1)).re := by
  classical
  dsimp only
  let g := ∏ p ∈ T, p
  let v := g / u
  have hgSq : Squarefree g := MediumSignedMainTerm.primeSubsetProduct_squarefree
    (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
    (Finset.mem_powerset.mp hT)
  have hudvd : u ∣ g := Nat.dvd_of_mem_divisors huMem
  have hu0 : 0 < u := Nat.pos_of_mem_divisors huMem
  have hguv : g = u * v := (Nat.mul_div_cancel' hudvd).symm
  have hv0 : 0 < v := by
    apply Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hgSq.ne_zero) hudvd)
    exact hu0
  letI : NeZero u := ⟨hu0.ne'⟩
  letI : NeZero v := ⟨hv0.ne'⟩
  have huv : Nat.Coprime u v := by
    apply Nat.coprime_of_squarefree_mul
    rw [← hguv]
    exact hgSq
  have hvSq : Squarefree v := by
    rw [hguv] at hgSq
    exact hgSq.of_mul_right
  have hgcop : Nat.Coprime g
      (CoverBPZ.refinementModulus S * C.val.otherValue i) := by
    simpa only [g] using
      MediumComplementBounds.window_product_coprime_complement hC hT
  have huMD := hgcop.of_dvd_left hudvd
  have hvdvd : v ∣ g := hguv ▸ dvd_mul_left v u
  have hvMD := hgcop.of_dvd_left hvdvd
  have hDv : Nat.Coprime
      (CoverBPZ.refinementModulus S * C.val.otherValue i) v := hvMD.symm
  have huQ : Nat.Coprime u
      (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) := by
    simpa only [Nat.mul_assoc] using huMD.mul_right huv
  have htQ : Nat.Coprime t
      (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) := by
    have h := (Finset.mem_filter.mp ht).2
    simpa only [Nat.mul_assoc, Nat.coprime_comm] using h
  have ht0 : 0 < t := (Nat.zero_le _).trans_lt
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp ht).1).1
  letI : NeZero t := ⟨ht0.ne'⟩
  letI : NeZero
      (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S)
      (Nat.mul_pos (C.val.otherValue_pos i) hv0)).ne'⟩
  have hd : u * t ∈ factors B X (C.val.otherValue i)
      (CoverBPZ.refinementModulus S) medium large := by
    change u * t ∈ GcdFactorReindex.interval
      (lower B X (C.val.otherValue i) medium)
      (upper X (C.val.otherValue i) large)
      (CoverBPZ.refinementModulus S * C.val.otherValue i)
    have hdf := (GcdFactorReindex.mul_mem_interval_filter_gcd_iff
      (A := lower B X (C.val.otherValue i) medium)
      (B := upper X (C.val.otherValue i) large)
      (Q := CoverBPZ.refinementModulus S * C.val.otherValue i)
      (v := v) hu0 huMD).mpr (by simpa only [Nat.mul_assoc] using ht)
    exact (Finset.mem_filter.mp hdf).1
  let E := fromFactor C i medium large (u * t)
  have hE : E ∈ certificates S X z medium large i :=
    (Finset.mem_filter.mp (fromFactor_mem_fibre C i hB
      (Finset.mem_filter.mp hC).2.2.2.2.2 hd)).1
  have hED : E.val.otherValue i = C.val.otherValue i :=
    MediumMassDecomposition.fromFactor_otherValue C i hd
  have hfactor : E.val.factor i = u * t := fromFactor_factor C i hd
  have hEDv : Nat.Coprime
      (CoverBPZ.refinementModulus S * E.val.otherValue i) v := by
    simpa only [hED] using hDv
  letI : NeZero
      (CoverBPZ.refinementModulus S * (E.val.otherValue i * v)) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S)
      (Nat.mul_pos (E.val.otherValue_pos i) hv0)).ne'⟩
  have hfullQuot := MediumCertificateZeroMode.gcd_quotient_coprime_classModulus
    E i hgSq (MediumComplementBounds.window_product_coprime_complement hE hT).symm
  have hgcd : Nat.gcd g (u * t) = u := by
    rw [hguv]
    have hvQ : v ∣ CoverBPZ.refinementModulus S * (C.val.otherValue i * v) := by
      use CoverBPZ.refinementModulus S * C.val.otherValue i
      ring
    have htv : Nat.Coprime v t := (htQ.of_dvd_right hvQ).symm
    exact (Erdos387Proof.gcd_mul_split_iff hu0).mpr
      htv
  have hquot : g / Nat.gcd g (E.val.factor i) = v := by
    rw [hfactor, hgcd]
  have hfull : Nat.Coprime
      (CoverBPZ.refinementModulus S * E.val.value) v := by
    simpa only [hquot] using hfullQuot
  letI : NeZero (g / Nat.gcd g (E.val.factor i)) :=
    ⟨by rw [hquot]; exact hv0.ne'⟩
  have huQE : Nat.Coprime u
      (CoverBPZ.refinementModulus S * (E.val.otherValue i * v)) := by
    simpa only [hED] using huQ
  have htQE : Nat.Coprime t
      (CoverBPZ.refinementModulus S * (E.val.otherValue i * v)) := by
    simpa only [hED] using htQ
  have hE' : fromFactor C i medium large (u * t) ∈
      certificates S X z medium large i := by exact hE
  have hwindow : windowCertificateNonzeroPartial i
      (fromFactor C i medium large (u * t)) z medium large H T =
      certificateNonzeroPartial E
        (g / Nat.gcd g (E.val.factor i)) H hfullQuot := by
    unfold windowCertificateNonzeroPartial
    simp only [dif_pos hE', dif_pos hT]
    rfl
  rw [hwindow]
  rw [certificateNonzeroPartial_congr E hfullQuot hfull hquot]
  rw [certificateNonzeroPartial_eq_masked E i hfactor hvSq hEDv hfull huQE htQE]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro h hh
  have hgamma := combinedResidue_eq_of_factors_eq_off_index
    E C i v a hEDv hDv (by
      intro j hji
      dsimp only [E]
      simp only [fromFactor, dif_pos hd, TupleReplacement.factor_replaceRefined,
        if_neg hji])
  apply congrArg Complex.re
  apply maskedFourierSummand_congr X
    (CoverBPZ.refinementModulus S * (E.val.otherValue i * v))
    (CoverBPZ.refinementModulus S * (C.val.otherValue i * v))
    u (combinedResidue E i v a hEDv) (combinedResidue C i v a hDv)
    i.val huQE huQ h t ht0
  · rw [hED]
  · exact hgamma

/-- One complete gcd block: compatible residual roots and nonzero integer
frequencies remain outside the full consecutive `t` interval. -/
noncomputable def gcdFourierBlock
    {B K X z medium large H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X} {T : Finset ℕ}
    (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset)
    (u : ℕ) : ℂ := by
  classical
  let g := ∏ p ∈ T, p
  by_cases huMem : u ∈ g.divisors
  ·
    let v := g / u
    have hgSq : Squarefree g := MediumSignedMainTerm.primeSubsetProduct_squarefree
      (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
      (Finset.mem_powerset.mp hT)
    have hu0 : 0 < u := Nat.pos_of_mem_divisors huMem
    have hv0 : 0 < v := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hgSq.ne_zero)
        (Nat.dvd_of_mem_divisors huMem))
      hu0
    letI : NeZero u := ⟨hu0.ne'⟩
    letI : NeZero v := ⟨hv0.ne'⟩
    have hguv : g = u * v :=
      (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors huMem)).symm
    have huv : Nat.Coprime u v := by
      apply Nat.coprime_of_squarefree_mul
      rw [← hguv]
      exact hgSq
    have hgcop : Nat.Coprime g
        (CoverBPZ.refinementModulus S * C.val.otherValue i) := by
      simpa only [g] using
        MediumComplementBounds.window_product_coprime_complement hC hT
    have hDv : Nat.Coprime
        (CoverBPZ.refinementModulus S * C.val.otherValue i) v := by
      apply Nat.Coprime.of_dvd_right _ hgcop.symm
      exact hguv ▸ dvd_mul_left v u
    have huQ : Nat.Coprime u
        (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) := by
      have huMD := hgcop.of_dvd_left (Nat.dvd_of_mem_divisors huMem)
      simpa only [Nat.mul_assoc] using huMD.mul_right huv
    letI : NeZero
        (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) :=
      ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S)
        (Nat.mul_pos (C.val.otherValue_pos i) hv0)).ne'⟩
    exact ∑ a ∈ localAssignmentResidues v S.k,
      ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
        ∑ r ∈ Finset.range
          (upper X (C.val.otherValue i) large / u -
            lower B X (C.val.otherValue i) medium / u),
          maskedFourierSummand X
            (CoverBPZ.refinementModulus S * (C.val.otherValue i * v))
            u (combinedResidue C i v a hDv) i.val huQ h
              (lower B X (C.val.otherValue i) medium / u + r + 1) (by
                exact Nat.zero_lt_succ _)
  · exact 0

set_option linter.style.haveILetI false in
/-- Exact full-fibre identity.  The real part is taken only after each full
gcd-block interval has been summed. -/
theorem sum_partialRemainder_eq_re_gcdFourierBlocks
    {B K X z medium large H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K}
    {i : Fin S.k} {C : RefinedTupleCertificate S X} {T : Finset ℕ}
    (hB : 0 < B) (hX : 0 < X) (hHX : 4 * B * H ≤ X)
    (hC : C ∈ certificates S X z medium large i)
    (hT : T ∈ (MediumSieveEuler.windowPrimes S.k z).powerset) :
    let g := ∏ p ∈ T, p
    (∑ d ∈ factors B X (C.val.otherValue i)
        (CoverBPZ.refinementModulus S) medium large,
      partialRemainder (fromFactor C i medium large d) i
        z medium large H T) =
      ∑ u ∈ g.divisors, (gcdFourierBlock (H := H) hC hT u).re := by
  classical
  dsimp only
  rw [sum_partialRemainder_eq_sum_windowCertificateNonzeroPartial
    hB hX hHX hC hT]
  rw [sum_windowCertificateNonzeroPartial_eq_gcdIntervals hC hT]
  apply Finset.sum_congr rfl
  intro u huMem
  let g := ∏ p ∈ T, p
  let v := g / u
  have hgSq : Squarefree g := MediumSignedMainTerm.primeSubsetProduct_squarefree
    (fun p hp => (MediumSieveEuler.mem_windowPrimes.mp hp).1)
    (Finset.mem_powerset.mp hT)
  have hu0 : 0 < u := Nat.pos_of_mem_divisors huMem
  have hv0 : 0 < v := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hgSq.ne_zero)
      (Nat.dvd_of_mem_divisors huMem))
    hu0
  letI : NeZero u := ⟨hu0.ne'⟩
  letI : NeZero v := ⟨hv0.ne'⟩
  have hguv : g = u * v :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors huMem)).symm
  have huv : Nat.Coprime u v := by
    apply Nat.coprime_of_squarefree_mul
    rw [← hguv]
    exact hgSq
  have hgcop : Nat.Coprime g
      (CoverBPZ.refinementModulus S * C.val.otherValue i) := by
    simpa only [g] using
      MediumComplementBounds.window_product_coprime_complement hC hT
  have hDv : Nat.Coprime
      (CoverBPZ.refinementModulus S * C.val.otherValue i) v := by
    apply Nat.Coprime.of_dvd_right _ hgcop.symm
    exact hguv ▸ dvd_mul_left v u
  have huQ : Nat.Coprime u
      (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) := by
    have huMD := hgcop.of_dvd_left (Nat.dvd_of_mem_divisors huMem)
    simpa only [Nat.mul_assoc] using huMD.mul_right huv
  letI : NeZero
      (CoverBPZ.refinementModulus S * (C.val.otherValue i * v)) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S)
      (Nat.mul_pos (C.val.otherValue_pos i) hv0)).ne'⟩
  let A := lower B X (C.val.otherValue i) medium / u
  let U := upper X (C.val.otherValue i) large / u
  let Q := CoverBPZ.refinementModulus S * (C.val.otherValue i * v)
  have hpoint (t : ℕ)
      (ht : t ∈ GcdFactorReindex.interval A U
        (CoverBPZ.refinementModulus S * (C.val.otherValue i * v))) :
      windowCertificateNonzeroPartial i
          (fromFactor C i medium large (u * t)) z medium large H T =
        ∑ a ∈ localAssignmentResidues v S.k,
          ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
            (totalMaskedFourierSummand X Q u
              (combinedResidue C i v a hDv) i.val huQ h t).re := by
    rw [windowCertificateNonzeroPartial_fromFactor_mul_eq_masked
      hB hC hT huMem ht]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro h hh
    have ht0 : 0 < t := (Nat.zero_le _).trans_lt
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp ht).1).1
    exact congrArg Complex.re
      (totalMaskedFourierSummand_of_pos X Q u
        (combinedResidue C i v a hDv) i.val huQ h t ht0).symm
  rw [Finset.sum_congr rfl hpoint]
  simp only [gcdFourierBlock, dif_pos huMem]
  dsimp only [g, v, A, U, Q]
  simp only [Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  have hinter := sum_interval_totalMasked_eq_range A U X Q u
    (combinedResidue C i v a hDv) i.val huQ h
  have hre := congrArg Complex.re hinter
  simp only [Complex.re_sum] at hre
  simpa only [A, U, Q, g, v] using hre

end Erdos387Proof.MediumFibreFourier
