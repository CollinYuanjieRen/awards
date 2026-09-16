import Erdos387Proof.MediumResidueFourier
import Erdos387Proof.BrunLocalDensity

/-! Actual medium certificate residue masses, including overlap of the
squarefree sieve modulus with the varying factor. -/

namespace Erdos387Proof.MediumCertificateZeroMode

open Erdos387 IntegerSieveResidues IntegerClassFourier MediumResidueFourier
open MediumSieveSmoothing
open scoped BigOperators

theorem squarefree_div_gcd_coprime {g d : ℕ} (hg : Squarefree g) :
    Nat.Coprime (g / Nat.gcd g d) d := by
  have hguv : g = Nat.gcd g d * (g / Nat.gcd g d) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left g d)).symm
  obtain ⟨t, hdt⟩ := Nat.gcd_dvd_right g d
  have hh := squarefree_gcd_split (t := t) hg hguv
  have hvt : Nat.Coprime (g / Nat.gcd g d) t := hh.2.mp (by rw [← hdt])
  simpa only [← hdt] using hh.1.symm.mul_right hvt

noncomputable def classRemainder {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (v : ℕ) [NeZero v]
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v) : ℝ := by
  let : NeZero (CoverBPZ.refinementModulus S * C.val.value) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos).ne'⟩
  exact residueRemainder X (CoverBPZ.refinementModulus S * C.val.value) v S.k
    (simultaneousResidue C.property (CoverBPZ.refinementResidue S) C.val.crtResidue) hcop

theorem residueMass_certificate_eq_main_add {B K X v : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} [NeZero v]
    (C : RefinedTupleCertificate S X) (hX : 0 < X) (hv : Squarefree v)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value) v)
    (hlarge : ∀ p ∈ v.primeFactors, S.k < p) :
    residueMass X v S.k (integerClass C) =
      (S.k : ℝ)^v.primeFactors.card *
        ((3*(X : ℝ)+1)/(CoverBPZ.refinementModulus S * C.val.value * v : ℕ)) +
          classRemainder C v hcop := by
  let : NeZero (CoverBPZ.refinementModulus S * C.val.value) :=
    ⟨(Nat.mul_pos (CoverBPZ.refinementModulus_pos S) C.val.value_pos).ne'⟩
  have heq : integerClass C =
      (fun n => Int.ModEq (CoverBPZ.refinementModulus S * C.val.value : ℕ) n
        (simultaneousResidue C.property (CoverBPZ.refinementResidue S) C.val.crtResidue : ℤ)) := by
    funext n
    exact propext (integerClass_iff_combined C n)
  rw [heq]
  exact residueMass_modEq_eq_main_add hX hv hcop hlarge

/-- Disjoint support on the fixed complement suffices: no roughness or
squarefreeness of the varying coordinate is required. -/
theorem gcd_quotient_coprime_classModulus {B K X g : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) (hg : Squarefree g)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) g) :
    Nat.Coprime (CoverBPZ.refinementModulus S * C.val.value)
      (g / Nat.gcd g (C.val.factor i)) := by
  have hvdvd : g / Nat.gcd g (C.val.factor i) ∣ g :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hMD := Nat.coprime_mul_iff_left.mp (hcop.of_dvd_right hvdvd)
  have hd := (squarefree_div_gcd_coprime (d := C.val.factor i) hg).symm
  rw [← C.val.factor_mul_otherValue i]
  exact hMD.1.mul_left (hd.mul_left hMD.2)

/-- Exact elimination of the overlapping gcd at the actual distinguished
coordinate of a medium certificate. -/
theorem residueMass_certificate_eq_gcd_quotient {B K X g : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) (hg : Squarefree g) :
    residueMass X g S.k (integerClass C) =
      residueMass X (g / Nat.gcd g (C.val.factor i)) S.k (integerClass C) := by
  apply residueMass_mul_eq hg
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left g (C.val.factor i))).symm
    (Nat.gcd_dvd_right g (C.val.factor i)) i.isLt
  intro n hn
  exact ((integerClass_iff_coordinate_split C i n).mp hn).2.2

end Erdos387Proof.MediumCertificateZeroMode
