import Erdos387Proof.ConvenientWeightedBox
import Erdos387Proof.ConvenientDyadicReduction

/-!
# The boxed split-pair fibre is the masked weighted double box

`ConvenientDyadicReduction.boxedPairs c r s` is the exact ordered split-pair
fibre of one active complementary vector inside one dyadic rectangle.  This
file identifies the sum of the real parts of the actual masked Fourier
summands over that fibre with the real part of
`ConvenientWeightedBox.boxSum`, i.e. with the weighted double sum over the
two independent `variableBox`es carrying the sharp near-product mask
`ConvenientWeightedMoment.sharpMask`.

The two ingredients are
* `mem_boxedPairs_iff_variableBox`: the exact domain identity
  `boxedPairs c r s = (variableBox g r medium c ×ˢ variableBox g s medium c)`
  filtered by the sharp window `r*s ≤ medium`, `X/2 < B*(D*r*s)`, `D*r*s ≤ X`,
  which is exactly the support of `sharpMask`; and
* `boxSummand_eq_weight`: the pointwise phase identity
  `maskedFourierSummand = tentWeight * momentKernel`, obtained from
  `ConvenientPhaseData.fourierSummand_eq_bilinear` (through
  `MediumWeightedPhase.maskedFourierSummand_eq`) together with
  `ConvenientWeightedMoment.momentKernel_eq_bilinear`.
-/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientBoxIdentity

open Erdos387 Erdos387.CoverBPZ
open ConvenientCertificateCover ConvenientComplementGrouping
open ConvenientSplitFibre ConvenientMomentBoxes ConvenientMomentBound
open ConvenientMomentApplicability ConvenientWeightedMoment ConvenientWeightedBox
open ConvenientDyadicReduction
open scoped BigOperators

/-- Membership in one independent variable box, unfolded. -/
theorem mem_variableBox_iff {B K X z y medium g b cut n : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} {c : Index S X z y medium i} :
    n ∈ variableBox g b cut c ↔
      n ∈ Finset.Ico (2^b) (2^(b+1)) ∧ y < n ∧ n ≤ medium ∧ n ≤ cut ∧
        IsZRough z n ∧
        n.Coprime (momentModulus (refinementModulus S) g (product c)) := by
  classical
  simp only [variableBox, Finset.mem_filter]

/-- The exact fibre identity: the boxed split-pair fibre is the product of the
two independent dyadic variable boxes cut by the sharp near-product window. -/
theorem mem_boxedPairs_iff_variableBox {B K N g r s : ℕ}
    {S : BPZSection6Input B K} {i : Fin S.k} (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) {p : ℕ × ℕ} :
    p ∈ boxedPairs c r s ↔
      (p.1 ∈ variableBox g r (SubpowerScale.medium N S.k) c ∧
        p.2 ∈ variableBox g s (SubpowerScale.medium N S.k) c) ∧
      (p.1*p.2 ≤ SubpowerScale.medium N S.k ∧
        SubpowerScale.X N S.k/2 < B*(product c*p.1*p.2) ∧
        product c*p.1*p.2 ≤ SubpowerScale.X N S.k) := by
  classical
  have hD := product_data c
  have hDeq : (complementRepresentative c).1.val.otherValue i = product c :=
    (product_eq_otherValue c).symm
  have hQ : momentModulus (refinementModulus S) g (product c)
      = refinementModulus S*product c*g := momentModulus_eq hD.1
  rw [mem_boxedPairs_iff, mem_splitPairDomain_iff, mem_variableBox_iff,
    mem_variableBox_iff, hQ]
  simp only [hDeq, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨⟨hy1,_⟩,⟨hy2,_⟩,hr1,hr2,hc1,hc2,hmed,hnear,hupper⟩,hI1,hI2⟩
    have hp1 : 0 < p.1 := (Nat.zero_le _).trans_lt hy1
    have hp2 : 0 < p.2 := (Nat.zero_le _).trans_lt hy2
    have hg1 : p.1.Coprime g :=
      (ConvenientPhaseData.coprime_of_support_rough hg.ne_zero
        (fun q hq => (hsupport q hq).2) hr1).symm
    have hg2 : p.2.Coprime g :=
      (ConvenientPhaseData.coprime_of_support_rough hg.ne_zero
        (fun q hq => (hsupport q hq).2) hr2).symm
    have h1med : p.1 ≤ SubpowerScale.medium N S.k :=
      (Nat.le_mul_of_pos_right p.1 hp2).trans hmed
    have h2med : p.2 ≤ SubpowerScale.medium N S.k :=
      (Nat.le_mul_of_pos_left p.2 hp1).trans hmed
    exact ⟨⟨⟨hI1,hy1,h1med,h1med,hr1,hc1.mul_right hg1⟩,
      ⟨hI2,hy2,h2med,h2med,hr2,hc2.mul_right hg2⟩⟩,hmed,hnear,hupper⟩
  · rintro ⟨⟨⟨hI1,hy1,h1med,_,hr1,hcop1⟩,⟨hI2,hy2,h2med,_,hr2,hcop2⟩⟩,
      hmed,hnear,hupper⟩
    have hp1 : 0 < p.1 := (Nat.zero_le _).trans_lt hy1
    have hp2 : 0 < p.2 := (Nat.zero_le _).trans_lt hy2
    have h1X : p.1 ≤ SubpowerScale.X N S.k :=
      ((Nat.le_mul_of_pos_left _ hD.1).trans
        (Nat.le_mul_of_pos_right _ hp2)).trans hupper
    have h2X : p.2 ≤ SubpowerScale.X N S.k :=
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos hD.1 hp1)).trans hupper
    exact ⟨⟨⟨hy1,h1X⟩,⟨hy2,h2X⟩,hr1,hr2,
      hcop1.coprime_dvd_right (dvd_mul_right _ g),
      hcop2.coprime_dvd_right (dvd_mul_right _ g),hmed,hnear,hupper⟩,hI1,hI2⟩

/-- The moment modulus of an active complement is the complement-fixed CRT
modulus `refinementModulus S * D * g` used by
`ConvenientFibreFourier.complementMaskedPartial`. -/
theorem modulus_eq {B K N g : ℕ} (S : BPZSection6Input B K) {i : Fin S.k}
    (c : ActualIndex S N i) :
    modulus S g (product c)
      = refinementModulus S*(complementRepresentative c).1.val.otherValue i*g := by
  rw [modulus, momentModulus_eq (product_data c).1, product_eq_otherValue c]

/-- The complementary residue carried by the moment phase of `c`; it is the
one used by `ConvenientMomentBound.phaseDifference`, hence by
`ConvenientWeightedMoment.momentKernel`. -/
noncomputable def boxGamma {B K N g : ℕ} (S : BPZSection6Input B K) (i : Fin S.k)
    (a : ℕ) (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) : ℕ :=
  MediumComplementFourier.combinedResidue (complementRepresentative c).1 i g a
    (ConvenientPhaseData.sieve_applicability (complementRepresentative_mem c)
      hg hsupport).2.2.1.symm

theorem phaseDifference_eq {B K N g : ℕ} {S : BPZSection6Input B K} {i : Fin S.k}
    (a : ℕ) (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) :
    phaseDifference a c hg hsupport
      = (boxGamma S i a hg hsupport c : ℤ)-(i.val : ℤ) := rfl

/-- The totalised masked Fourier summand of one ordered split pair.  Off the
actual arithmetic domain it is zero; on it, `boxSummand_eq` identifies it with
`MediumWeightedPhase.maskedFourierSummand`, which is the summand produced by
`ConvenientFibreFourier.complementMaskedPartial`. -/
noncomputable def boxSummand {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) (p : ℕ × ℕ) : ℂ :=
  if hp : 0 < p.1 ∧ 0 < p.2 ∧ p.1.Coprime (modulus S g (product c)) then
    haveI : NeZero p.1 := ⟨hp.1.ne'⟩
    MediumWeightedPhase.maskedFourierSummand (SubpowerScale.X N S.k)
      (modulus S g (product c)) p.1 (boxGamma S i a hg hsupport c) i.val
      hp.2.2 h p.2 hp.2.1
  else 0

set_option maxHeartbeats 1000000 in
theorem boxSummand_eq {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) {p : ℕ × ℕ} [NeZero p.1] (hp2 : 0 < p.2)
    (hcop : p.1.Coprime (modulus S g (product c))) :
    boxSummand S i a h hg hsupport c p =
      MediumWeightedPhase.maskedFourierSummand (SubpowerScale.X N S.k)
        (modulus S g (product c)) p.1 (boxGamma S i a hg hsupport c) i.val
        hcop h p.2 hp2 := by
  have hc : 0 < p.1 ∧ 0 < p.2 ∧ p.1.Coprime (modulus S g (product c)) :=
    ⟨NeZero.pos p.1, hp2, hcop⟩
  rw [boxSummand, dif_pos hc]

set_option linter.style.haveILetI false in
/-- The pointwise phase identity: on the actual domain the masked Fourier
summand is the tent weight times the moment kernel. -/
theorem boxSummand_eq_weight {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) {p : ℕ × ℕ} (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (hcop1 : p.1.Coprime (modulus S g (product c)))
    (hcop2 : p.2.Coprime (modulus S g (product c))) :
    boxSummand S i a h hg hsupport c p =
      FourierVariation.tentWeight (SubpowerScale.X N S.k) h (-(i.val : ℤ))
        ((modulus S g (product c) : ℝ)*p.1*p.2)⁻¹*
        momentKernel S i a h hg hsupport c p.1 p.2 := by
  classical
  haveI : NeZero p.1 := ⟨hp1.ne'⟩
  rw [boxSummand_eq S i a h hg hsupport c hp2 hcop1,
    MediumWeightedPhase.maskedFourierSummand_eq, momentKernel_eq_bilinear]
  have hcast : ((modulus S g (product c)*p.1*p.2 : ℕ) : ℝ)
      = (modulus S g (product c) : ℝ)*p.1*p.2 := by push_cast; ring
  have hk : Erdos387.Kloosterman.coefficient (modulus S g (product c))
      (MediumWeightedPhase.reciprocalCoefficient (modulus S g (product c)) p.1
        (boxGamma S i a hg hsupport c) i.val h)
      ((p.2 : ℕ) : ZMod (modulus S g (product c)))
      = ZMod.stdAddChar ((((-h)*phaseDifference a c hg hsupport : ℤ) :
          ZMod (modulus S g (product c)))*
          (p.1 : ZMod (modulus S g (product c)))⁻¹*
          (p.2 : ZMod (modulus S g (product c)))⁻¹) := by
    rw [Erdos387.Kloosterman.coefficient,
      if_pos ((ZMod.isUnit_iff_coprime p.2 (modulus S g (product c))).mpr hcop2),
      MediumWeightedPhase.reciprocalCoefficient, phaseDifference_eq a hg hsupport c]
  rw [hcast, hk]

/-- The unmasked weight of the double box: tent weight times moment kernel. -/
noncomputable def boxWeight {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) (u v : ℕ) : ℂ :=
  FourierVariation.tentWeight (SubpowerScale.X N S.k) h (-(i.val : ℤ))
    ((modulus S g (product c) : ℝ)*u*v)⁻¹*momentKernel S i a h hg hsupport c u v

theorem boxSum_eq_sum_boxWeight {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (r s a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) :
    boxSum S i r s a h hg hsupport c =
      ∑ u ∈ variableBox g r (SubpowerScale.medium N S.k) c,
      ∑ v ∈ variableBox g s (SubpowerScale.medium N S.k) c,
        sharpMask B (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k)
          (product c) u v*boxWeight S i a h hg hsupport c u v := rfl

/-- **The boxed fibre identity.**  The sum of the real parts of the actual
masked Fourier summands over the exact boxed split-pair fibre equals the real
part of the weighted double box sum carrying the sharp near-product mask. -/
theorem boxedPairs_sum_boxSummand_eq_boxSum {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (r s a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) :
    (∑ p ∈ boxedPairs c r s, (boxSummand S i a h hg hsupport c p).re) =
      (boxSum S i r s a h hg hsupport c).re := by
  classical
  have hpoint : ∀ p ∈ boxedPairs c r s,
      (boxSummand S i a h hg hsupport c p).re
        = (boxWeight S i a h hg hsupport c p.1 p.2).re := by
    intro p hp
    obtain ⟨⟨h1,h2⟩,_⟩ := (mem_boxedPairs_iff_variableBox hg hsupport c).mp hp
    obtain ⟨_,hy1,_,_,_,hcop1⟩ := mem_variableBox_iff.mp h1
    obtain ⟨_,hy2,_,_,_,hcop2⟩ := mem_variableBox_iff.mp h2
    exact congrArg Complex.re (boxSummand_eq_weight S i a h hg hsupport c
      ((Nat.zero_le _).trans_lt hy1) ((Nat.zero_le _).trans_lt hy2) hcop1 hcop2)
  rw [Finset.sum_congr rfl hpoint, ← Complex.re_sum]
  refine congrArg Complex.re ?_
  have hmask : ∀ u v : ℕ,
      sharpMask B (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k)
          (product c) u v*boxWeight S i a h hg hsupport c u v
        = if u*v ≤ SubpowerScale.medium N S.k ∧
            SubpowerScale.X N S.k/2 < B*(product c*u*v) ∧
            product c*u*v ≤ SubpowerScale.X N S.k then
            boxWeight S i a h hg hsupport c u v else 0 := by
    intro u v
    by_cases hc : u*v ≤ SubpowerScale.medium N S.k ∧
        SubpowerScale.X N S.k/2 < B*(product c*u*v) ∧
        product c*u*v ≤ SubpowerScale.X N S.k
    · rw [if_pos hc, sharpMask, if_pos hc, one_mul]
    · rw [if_neg hc, sharpMask, if_neg hc, zero_mul]
  have hdomain : boxedPairs c r s =
      ((variableBox g r (SubpowerScale.medium N S.k) c) ×ˢ
        (variableBox g s (SubpowerScale.medium N S.k) c)).filter
        (fun p => p.1*p.2 ≤ SubpowerScale.medium N S.k ∧
          SubpowerScale.X N S.k/2 < B*(product c*p.1*p.2) ∧
          product c*p.1*p.2 ≤ SubpowerScale.X N S.k) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_product,
      mem_boxedPairs_iff_variableBox hg hsupport c]
  symm
  calc boxSum S i r s a h hg hsupport c
      = ∑ u ∈ variableBox g r (SubpowerScale.medium N S.k) c,
        ∑ v ∈ variableBox g s (SubpowerScale.medium N S.k) c,
          sharpMask B (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k)
            (product c) u v*boxWeight S i a h hg hsupport c u v :=
        boxSum_eq_sum_boxWeight S i r s a h hg hsupport c
    _ = ∑ p ∈ (variableBox g r (SubpowerScale.medium N S.k) c) ×ˢ
          (variableBox g s (SubpowerScale.medium N S.k) c),
          sharpMask B (SubpowerScale.X N S.k) (SubpowerScale.medium N S.k)
            (product c) p.1 p.2*boxWeight S i a h hg hsupport c p.1 p.2 :=
        (Finset.sum_product' _ _ _).symm
    _ = ∑ p ∈ (variableBox g r (SubpowerScale.medium N S.k) c) ×ˢ
          (variableBox g s (SubpowerScale.medium N S.k) c),
          if p.1*p.2 ≤ SubpowerScale.medium N S.k ∧
              SubpowerScale.X N S.k/2 < B*(product c*p.1*p.2) ∧
              product c*p.1*p.2 ≤ SubpowerScale.X N S.k then
            boxWeight S i a h hg hsupport c p.1 p.2 else 0 :=
        Finset.sum_congr rfl (fun p _ => hmask p.1 p.2)
    _ = ∑ p ∈ ((variableBox g r (SubpowerScale.medium N S.k) c) ×ˢ
          (variableBox g s (SubpowerScale.medium N S.k) c)).filter
          (fun p => p.1*p.2 ≤ SubpowerScale.medium N S.k ∧
            SubpowerScale.X N S.k/2 < B*(product c*p.1*p.2) ∧
            product c*p.1*p.2 ≤ SubpowerScale.X N S.k),
          boxWeight S i a h hg hsupport c p.1 p.2 := (Finset.sum_filter _ _).symm
    _ = ∑ p ∈ boxedPairs c r s, boxWeight S i a h hg hsupport c p.1 p.2 := by
        rw [hdomain]

/-- The form the outer summation consumes: any real weight agreeing with the
masked summand on the fibre sums to the real part of the box sum. -/
theorem boxedPairs_sum_eq_boxSum {B K N g : ℕ} (S : BPZSection6Input B K)
    (i : Fin S.k) (r s a : ℕ) (h : ℤ) [NeZero g] (hg : Squarefree g)
    (hsupport : ∀ q ∈ g.primeFactors, max (2*S.k) 3 ≤ q ∧ q < SubpowerScale.z N S.k)
    (c : ActualIndex S N i) (F : ℕ × ℕ → ℝ)
    (hF : ∀ p ∈ boxedPairs c r s, F p = (boxSummand S i a h hg hsupport c p).re) :
    (∑ p ∈ boxedPairs c r s, F p) = (boxSum S i r s a h hg hsupport c).re := by
  rw [Finset.sum_congr rfl hF]
  exact boxedPairs_sum_boxSummand_eq_boxSum S i r s a h hg hsupport c

end Erdos387Proof.ConvenientBoxIdentity
