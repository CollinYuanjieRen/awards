import Erdos387Proof.MediumFourierReduction

/-! The retained partial remainder is the explicit common-integer-window
sum with zero removed. The subtraction introduces no new hypothesis. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumPartialFourier

open Erdos387 TentFourier MediumFourierTail MediumCertificateZeroMode
open MediumMassDecomposition IntegerSieveResidues IntegerClassFourier
open scoped BigOperators

noncomputable def nonzeroPartial (X q H : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ h ∈ (IntegerFourierWindow.window H).erase 0,
    ZMod.stdAddChar (-(h : ZMod q) * a) * TentFourier.coefficient X q (h : ZMod q)

theorem integerPartial_eq_zero_add {X q H : ℕ} [NeZero q]
    (hX : 0 < X) (a : ZMod q) :
    (∑ h ∈ IntegerFourierWindow.window H,
      ZMod.stdAddChar (-(h : ZMod q) * a) *
        TentFourier.coefficient X q (h : ZMod q)).re =
      (3 * (X : ℝ) + 1) / q + (nonzeroPartial X q H a).re := by
  classical
  have hz : (0 : ℤ) ∈ IntegerFourierWindow.window H := by
    simp [IntegerFourierWindow.window]
  rw [← Finset.add_sum_erase _ _ hz]
  simp only [Int.cast_zero, neg_zero, zero_mul, AddChar.map_zero_eq_one, one_mul,
    coefficient_zero hX, Complex.add_re]
  have he : (3 * (X : ℂ) + 1) / (q : ℂ) =
      (((3 * (X : ℝ) + 1) / q : ℝ) : ℂ) := by push_cast; rfl
  rw [he]
  rfl

noncomputable def certificateNonzeroPartial {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (v H : ℕ) [NeZero v]
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v) : ℝ := by
  let : NeZero (CoverBPZ.refinementModulus S * C.val.value) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos).ne'⟩
  exact ∑ a ∈ localAssignmentResidues v S.k,
    (nonzeroPartial X (CoverBPZ.refinementModulus S * C.val.value * v) H
      (simultaneousResidue hcop
        (simultaneousResidue C.property (CoverBPZ.refinementResidue S) C.val.crtResidue)
        a : ZMod (CoverBPZ.refinementModulus S * C.val.value * v))).re

/-- Exact local-root multiplicity for the partial zero frequency. -/
theorem certificatePartial_eq_zero_add {B K X v H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X) [NeZero v]
    (hX : 0 < X)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v)
    (hlarge : ∀ p ∈ v.primeFactors, S.k < p)
    (hHq : 2 * H < CoverBPZ.refinementModulus S * C.val.value * v) :
    certificatePartial C v H hcop =
      (S.k : ℝ)^v.primeFactors.card *
        ((3 * (X : ℝ) + 1) / (CoverBPZ.refinementModulus S * C.val.value * v : ℕ)) +
      certificateNonzeroPartial C v H hcop := by
  let : NeZero (CoverBPZ.refinementModulus S * C.val.value) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos).ne'⟩
  rw [certificatePartial_eq_integer C hcop hHq]
  unfold certificateIntegerPartial
  simp_rw [integerPartial_eq_zero_add hX]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, card_localAssignmentResidues hlarge,
    Nat.cast_pow, certificateNonzeroPartial]

/-- The gcd-overlap zero coefficient agrees with the explicit Fourier
coefficient; the residual frequencies are precisely 0<|h|≤H. -/
theorem certificatePartial_sub_zeroCoefficient {B K X g H : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) [NeZero (g / Nat.gcd g (C.val.factor i))]
    (hX : 0 < X) (hg : Squarefree g)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) g)
    (hlarge : ∀ p ∈ g.primeFactors, S.k < p)
    (hHq : 2 * H < CoverBPZ.refinementModulus S * C.val.value *
      (g / Nat.gcd g (C.val.factor i))) :
    certificatePartial C (g / Nat.gcd g (C.val.factor i)) H
        (gcd_quotient_coprime_classModulus C i hg hcop) - zeroCoefficient C i g =
      certificateNonzeroPartial C (g / Nat.gcd g (C.val.factor i)) H
        (gcd_quotient_coprime_classModulus C i hg hcop) := by
  have hvdvd : g / Nat.gcd g (C.val.factor i) ∣ g :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  rw [certificatePartial_eq_zero_add C hX _
    (fun p hp => hlarge p (Nat.primeFactors_mono hvdvd hg.ne_zero hp)) hHq]
  have hden : CoverBPZ.refinementModulus S * C.val.value *
      (g / Nat.gcd g (C.val.factor i)) =
      CoverBPZ.refinementModulus S * C.val.otherValue i *
        (g / Nat.gcd g (C.val.factor i)) * C.val.factor i := by
    rw [← C.val.factor_mul_otherValue i]
    ring
  rw [hden]
  unfold zeroCoefficient
  ring

end Erdos387Proof.MediumPartialFourier
