import Erdos387Proof.IntegerClassFourier
import Erdos387Proof.TupleReplacement

/-! Fourier classes in the order needed for inverse sums: first combine the
fixed progression, complementary tuple and sieve residue, then the varying
coordinate. The first combined residue is independent of that coordinate. -/

namespace Erdos387Proof.MediumComplementFourier

open Erdos387 Erdos387Proof.IntegerSieveResidues Erdos387Proof.IntegerClassFourier
open Erdos387Proof.TentFourier
open scoped BigOperators

theorem fixed_complement_coprime {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) :
    Nat.Coprime (CoverBPZ.refinementModulus S) (C.val.otherValue i) :=
  C.property.of_dvd_right (by
    rw [← C.val.factor_mul_otherValue i]
    exact dvd_mul_left _ _)

noncomputable def combinedResidue {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) (v a : ℕ)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) v) : ℕ :=
  simultaneousResidue hcop
    (simultaneousResidue (fixed_complement_coprime C i)
      (CoverBPZ.refinementResidue S) (C.val.otherResidue i)) a

theorem combined_coprime_factor {B K X : ℕ} {S : CoverBPZ.BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (i : Fin S.k) {v : ℕ}
    (hvd : Nat.Coprime v (C.val.factor i)) :
    Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i * v)
      (C.val.factor i) := by
  have hMd : Nat.Coprime (CoverBPZ.refinementModulus S) (C.val.factor i) :=
    C.property.of_dvd_right (by
      rw [← C.val.factor_mul_otherValue i]
      exact dvd_mul_right _ _)
  exact (hMd.mul_left (C.val.otherValue_coprime_factor i)).mul_left hvd

theorem integerClass_and_residue_iff {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) (v a : ℕ) (hv : 0 < v) (ha : a < v)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) v)
    (hvd : Nat.Coprime v (C.val.factor i)) (n : ℤ) :
    (MediumSieveSmoothing.integerClass C n ∧ (n % (v : ℤ)).toNat = a) ↔
      Int.ModEq ((CoverBPZ.refinementModulus S * C.val.otherValue i * v) *
        C.val.factor i : ℕ) n
        (simultaneousResidue (combined_coprime_factor C i hvd)
          (combinedResidue C i v a hcop) i.val : ℤ) := by
  rw [integerClass_iff_coordinate_split C i n, natResidue_eq_iff_modEq n hv ha]
  rw [← simultaneous_modEq_iff (combined_coprime_factor C i hvd)]
  unfold combinedResidue
  rw [← simultaneous_modEq_iff hcop, ← simultaneous_modEq_iff (fixed_complement_coprime C i)]
  tauto

/-- Exact class mass with the varying coordinate placed last in the CRT. -/
theorem classMass_eq_complement_progressionMass {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) (v a : ℕ) [NeZero v] (ha : a < v)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) v)
    (hvd : Nat.Coprime v (C.val.factor i)) :
    letI : NeZero (CoverBPZ.refinementModulus S) := ⟨(CoverBPZ.refinementModulus_pos S).ne'⟩
    letI : NeZero (C.val.otherValue i) := ⟨(C.val.otherValue_pos i).ne'⟩
    letI : NeZero (C.val.factor i) := ⟨(C.val.positive i).ne'⟩
    classMass X v a (MediumSieveSmoothing.integerClass C) =
      progressionMass X ((CoverBPZ.refinementModulus S * C.val.otherValue i * v) *
        C.val.factor i)
        (simultaneousResidue (combined_coprime_factor C i hvd)
          (combinedResidue C i v a hcop) i.val :
            ZMod ((CoverBPZ.refinementModulus S * C.val.otherValue i * v) * C.val.factor i)) := by
  classical
  unfold classMass progressionMass
  apply Finset.sum_congr rfl
  intro n hn
  have hiff := integerClass_and_residue_iff C i v a (NeZero.pos v) ha hcop hvd n
  have hz := ZMod.intCast_eq_intCast_iff n
    (simultaneousResidue (combined_coprime_factor C i hvd)
      (combinedResidue C i v a hcop) i.val : ℤ)
    ((CoverBPZ.refinementModulus S * C.val.otherValue i * v) * C.val.factor i)
  have heq := hiff.trans hz.symm
  simp only [Int.cast_natCast] at heq
  simp only [heq, mul_ite, mul_one, mul_zero]

/-- The complementary residue remains fixed under replacement of the
distinguished factor. -/
theorem combinedResidue_eq_of_factors_eq_off_index {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C E : RefinedTupleCertificate S X)
    (i : Fin S.k) (v a : ℕ)
    (hC : Nat.Coprime (CoverBPZ.refinementModulus S * C.val.otherValue i) v)
    (hE : Nat.Coprime (CoverBPZ.refinementModulus S * E.val.otherValue i) v)
    (hfactor : ∀ j, j ≠ i → C.val.factor j = E.val.factor j) :
    combinedResidue C i v a hC = combinedResidue E i v a hE := by
  have hD := otherValue_eq_of_factors_eq_off_index C.val E.val i hfactor
  have hr := otherResidue_eq_of_factors_eq_off_index C.val E.val i hfactor
  simp only [combinedResidue, hD, hr]

end Erdos387Proof.MediumComplementFourier
