import Erdos387Proof.MediumCertificateZeroMode
import Erdos387Proof.MediumZeroModeIdentity
import Erdos387Proof.MediumFactorWindow

/-! Exact splitting of the actual complementary-fibre mass. The remainder
is identified with the explicit nonzero Fourier sum under the arithmetic
conditions already supplied by the certificate adapters. -/

namespace Erdos387Proof.MediumMassDecomposition

open Erdos387 MediumFactorWindow MediumCertificateZeroMode
open IntegerSieveResidues MediumSieveSmoothing
open scoped BigOperators

noncomputable def zeroCoefficient {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (g : ℕ) : ℝ :=
  (S.k : ℝ) ^ (g / Nat.gcd g (C.val.factor i)).primeFactors.card *
    ((3 * (X : ℝ) + 1) /
      (CoverBPZ.refinementModulus S * C.val.otherValue i *
        (g / Nat.gcd g (C.val.factor i)) * C.val.factor i : ℕ))

noncomputable def remainder {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (g : ℕ) : ℝ :=
  residueMass X g S.k (integerClass C) - zeroCoefficient C i g

/-- The named remainder is exactly the nonzero Fourier sum, with compatible
sieve roots counted once after the gcd overlap is removed. -/
theorem remainder_eq_explicit_fourier {B K X g : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) [NeZero (g / Nat.gcd g (C.val.factor i))]
    (hX : 0 < X) (hg : Squarefree g)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) g)
    (hlarge : ∀ p ∈ g.primeFactors, S.k < p) :
    remainder C i g = classRemainder C (g / Nat.gcd g (C.val.factor i))
      (gcd_quotient_coprime_classModulus C i hg hcop) := by
  have hvdvd : g / Nat.gcd g (C.val.factor i) ∣ g :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hv := hg.squarefree_of_dvd hvdvd
  have hlargeV : ∀ p ∈ (g / Nat.gcd g (C.val.factor i)).primeFactors, S.k < p :=
    fun p hp => hlarge p (Nat.primeFactors_mono hvdvd hg.ne_zero hp)
  unfold remainder
  rw [residueMass_certificate_eq_gcd_quotient C i hg,
    residueMass_certificate_eq_main_add C hX hv
      (gcd_quotient_coprime_classModulus C i hg hcop) hlargeV]
  have hden : CoverBPZ.refinementModulus S * C.val.value *
        (g / Nat.gcd g (C.val.factor i)) =
      CoverBPZ.refinementModulus S * C.val.otherValue i *
        (g / Nat.gcd g (C.val.factor i)) * C.val.factor i := by
    rw [← C.val.factor_mul_otherValue i]
    ring
  rw [hden]
  unfold zeroCoefficient
  ring

theorem fromFactor_otherValue {B K X medium large d : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k)
    (hd : d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large) :
    (fromFactor C i medium large d).val.otherValue i = C.val.otherValue i := by
  classical
  unfold fromFactor
  rw [dif_pos hd]
  apply otherValue_eq_of_factors_eq_off_index
  intro j hj
  simp only [TupleReplacement.factor_replaceRefined, if_neg hj]

theorem sum_zeroCoefficient_eq_zeroMode {B K X g medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) (hg : 0 < g)
    (hcop : Nat.Coprime g (CoverBPZ.refinementModulus S * C.val.otherValue i)) :
    (∑ d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large,
      zeroCoefficient (fromFactor C i medium large d) i g) =
      MediumZeroMode.zeroMode g (CoverBPZ.refinementModulus S * C.val.otherValue i) S.k
        (lower B X (C.val.otherValue i) medium) (upper X (C.val.otherValue i) large)
        (3 * (X : ℝ) + 1) := by
  have heach (d : ℕ)
      (hd : d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large) :
      zeroCoefficient (fromFactor C i medium large d) i g =
        (S.k : ℝ) ^ (g / Nat.gcd g d).primeFactors.card *
          ((3 * (X : ℝ) + 1) /
            ((CoverBPZ.refinementModulus S * C.val.otherValue i) * (g / Nat.gcd g d) * d : ℕ)) := by
    simp only [zeroCoefficient, fromFactor_factor C i hd, fromFactor_otherValue C i hd]
  rw [Finset.sum_congr rfl heach]
  exact MediumZeroModeIdentity.sum_zeroCoefficients_eq_zeroMode hg hcop _

/-- No inequality has been used: the actual residue masses equal their
harmonic zero mode plus the explicit Fourier remainder of every factor. -/
theorem sum_residueMass_eq_zeroMode_add_remainder {B K X g medium large : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) (hg : 0 < g)
    (hcop : Nat.Coprime g (CoverBPZ.refinementModulus S * C.val.otherValue i)) :
    (∑ d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large,
      residueMass X g S.k (integerClass (fromFactor C i medium large d))) =
      MediumZeroMode.zeroMode g (CoverBPZ.refinementModulus S * C.val.otherValue i) S.k
        (lower B X (C.val.otherValue i) medium) (upper X (C.val.otherValue i) large)
        (3 * (X : ℝ) + 1) +
      ∑ d ∈ factors B X (C.val.otherValue i) (CoverBPZ.refinementModulus S) medium large,
        remainder (fromFactor C i medium large d) i g := by
  rw [← sum_zeroCoefficient_eq_zeroMode C i hg hcop]
  simp only [remainder, Finset.sum_sub_distrib]
  ring

end Erdos387Proof.MediumMassDecomposition
