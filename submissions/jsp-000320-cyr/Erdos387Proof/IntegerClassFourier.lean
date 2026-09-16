import Erdos387Proof.IntegerSieveResidues

/-! CRT and the actual finite Fourier expansion of integer class masses. -/

namespace Erdos387Proof.IntegerClassFourier

open Erdos387 Erdos387Proof.IntegerSieveResidues Erdos387Proof.TentFourier
open scoped BigOperators

theorem natResidue_eq_iff_modEq (n : ℤ) {v a : ℕ} (hv : 0 < v) (ha : a < v) :
    (n % (v : ℤ)).toNat = a ↔ Int.ModEq (v : ℤ) n (a : ℤ) := by
  have hnonneg : 0 ≤ n % (v : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hv.ne')
  have hamod : (a : ℤ) % (v : ℤ) = a := by exact_mod_cast Nat.mod_eq_of_lt ha
  rw [Int.ModEq, hamod]
  constructor
  · intro h
    calc
      n % (v : ℤ) = (((n % (v : ℤ)).toNat : ℕ) : ℤ) :=
        (Int.toNat_of_nonneg hnonneg).symm
      _ = a := by rw [h]
  · intro h
    rw [h, Int.toNat_natCast]

theorem simultaneous_modEq_iff {M d : ℕ} (hcop : Nat.Coprime M d)
    (a b : ℕ) (n : ℤ) :
    Int.ModEq (M : ℤ) n (a : ℤ) ∧ Int.ModEq (d : ℤ) n (b : ℤ) ↔
      Int.ModEq (M * d : ℕ) n (simultaneousResidue hcop a b : ℤ) := by
  have hM : Int.ModEq (M : ℤ) (simultaneousResidue hcop a b : ℤ) (a : ℤ) :=
    Int.natCast_modEq_iff.mpr (simultaneousResidue_mod_left hcop a b)
  have hd : Int.ModEq (d : ℤ) (simultaneousResidue hcop a b : ℤ) (b : ℤ) :=
    Int.natCast_modEq_iff.mpr (simultaneousResidue_mod_right hcop a b)
  have hc : (M : ℤ).natAbs.Coprime (d : ℤ).natAbs := by simpa using hcop
  rw [Nat.cast_mul, ← Int.modEq_and_modEq_iff_modEq_mul hc]
  exact ⟨fun h => ⟨h.1.trans hM.symm, h.2.trans hd.symm⟩,
    fun h => ⟨h.1.trans hM, h.2.trans hd⟩⟩

theorem classMass_eq_progressionMass (X Q v a b : ℕ) [NeZero Q] [NeZero v]
    (hcop : Nat.Coprime Q v) (ha : a < v) :
    classMass X v a (fun n => Int.ModEq (Q : ℤ) n (b : ℤ)) =
      progressionMass X (Q * v) (simultaneousResidue hcop b a : ZMod (Q * v)) := by
  classical
  unfold classMass progressionMass
  apply Finset.sum_congr rfl
  intro n hn
  have hiff : (Int.ModEq (Q : ℤ) n (b : ℤ) ∧ (n % (v : ℤ)).toNat = a) ↔
      (n : ZMod (Q * v)) = (simultaneousResidue hcop b a : ZMod (Q * v)) := by
    rw [natResidue_eq_iff_modEq n (NeZero.pos v) ha, simultaneous_modEq_iff hcop]
    simpa using (ZMod.intCast_eq_intCast_iff n
      (simultaneousResidue hcop b a : ℤ) (Q * v)).symm
  simp only [hiff, mul_ite, mul_one, mul_zero]

/-- Finite Fourier inversion for the actual integer class mass, including
negative points of the tent support. -/
theorem classMass_eq_fourier (X Q v a b : ℕ) [NeZero Q] [NeZero v]
    (hcop : Nat.Coprime Q v) (ha : a < v) :
    (classMass X v a (fun n => Int.ModEq (Q : ℤ) n (b : ℤ)) : ℂ) =
      ∑ h : ZMod (Q * v),
        ZMod.stdAddChar (-h * (simultaneousResidue hcop b a : ZMod (Q * v))) *
          coefficient X (Q * v) h := by
  rw [classMass_eq_progressionMass X Q v a b hcop ha, progressionMass_eq_fourier]

theorem integerClass_iff_combined {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X) (n : ℤ) :
    MediumSieveSmoothing.integerClass C n ↔
      Int.ModEq (CoverBPZ.refinementModulus S * C.val.value : ℕ) n
        (simultaneousResidue C.property (CoverBPZ.refinementResidue S) C.val.crtResidue : ℤ) :=
  simultaneous_modEq_iff C.property _ _ n

end Erdos387Proof.IntegerClassFourier
