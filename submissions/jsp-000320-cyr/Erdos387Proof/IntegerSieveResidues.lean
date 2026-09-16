import Erdos387Proof.MediumSieveSmoothing
import Erdos387Proof.ComplementResidue

/-! Exact elimination of the overlapping sieve factor and decomposition of
integer sieve masses into canonical residue classes. -/

namespace Erdos387Proof.IntegerSieveResidues

open Erdos387 Erdos387Proof.IntegerBrunSmoothing Erdos387Proof.TentFourier
open scoped BigOperators

theorem residue_allowed_mul_iff {g u v d k i : ℕ} (n : ℤ)
    (hg : Squarefree g) (hguv : g = u * v) (hud : u ∣ d) (hi : i < k)
    (hn : Int.ModEq (d : ℤ) n (i : ℤ)) :
    (n % (g : ℤ)).toNat ∈ localAssignmentResidues g k ↔
      (n % (v : ℤ)).toNat ∈ localAssignmentResidues v k := by
  have hvdvd : v ∣ g := hguv.symm ▸ dvd_mul_left v u
  have hv : Squarefree v := hg.squarefree_of_dvd hvdvd
  rw [residue_mem_localAssignmentResidues_iff n hg,
    residue_mem_localAssignmentResidues_iff n hv]
  constructor
  · intro h p hp
    exact h p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1, (Nat.dvd_of_mem_primeFactors hp).trans hvdvd,
        hg.ne_zero⟩)
  · intro h p hp
    have hprime := (Nat.mem_primeFactors.mp hp).1
    have hpguv : p ∣ u * v := hguv ▸ Nat.dvd_of_mem_primeFactors hp
    rcases hprime.dvd_mul.mp hpguv with hpu | hpv
    · have hmod : Int.ModEq (p : ℤ) n (i : ℤ) :=
        hn.of_dvd (by exact_mod_cast hpu.trans hud)
      have heq : n % (p : ℤ) = (i : ℤ) % (p : ℤ) := hmod
      rw [heq, ← Int.natCast_mod, Int.toNat_natCast]
      exact (Nat.mod_le i p).trans_lt hi
    · exact h p (Nat.mem_primeFactors.mpr ⟨hprime, hpv, hv.ne_zero⟩)

theorem integerClass_iff_coordinate_split {B K X : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} (C : RefinedTupleCertificate S X)
    (i : Fin S.k) (n : ℤ) :
    MediumSieveSmoothing.integerClass C n ↔
      Int.ModEq (CoverBPZ.refinementModulus S : ℤ) n (CoverBPZ.refinementResidue S : ℤ) ∧
      Int.ModEq (C.val.otherValue i : ℤ) n (C.val.otherResidue i : ℤ) ∧
      Int.ModEq (C.val.factor i : ℤ) n (i.val : ℤ) := by
  have hD : Int.ModEq (C.val.otherValue i : ℤ) (C.val.crtResidue : ℤ)
      (C.val.otherResidue i : ℤ) :=
    Int.natCast_modEq_iff.mpr (C.val.crtResidue_modEq_otherResidue i)
  have hd : Int.ModEq (C.val.factor i : ℤ) (C.val.crtResidue : ℤ) (i.val : ℤ) :=
    Int.natCast_modEq_iff.mpr (C.val.crtResidue_mod_factor i)
  have hprod : (C.val.value : ℤ) = (C.val.otherValue i : ℤ) * (C.val.factor i : ℤ) := by
    exact_mod_cast (C.val.otherValue_mul_factor i).symm
  have hcop : (C.val.otherValue i : ℤ).natAbs.Coprime (C.val.factor i : ℤ).natAbs := by
    simpa using C.val.otherValue_coprime_factor i
  constructor
  · rintro ⟨hM, hC⟩
    rw [hprod] at hC
    obtain ⟨hnD, hnd⟩ := (Int.modEq_and_modEq_iff_modEq_mul hcop).mpr hC
    exact ⟨hM, hnD.trans hD, hnd.trans hd⟩
  · rintro ⟨hM, hnD, hnd⟩
    refine ⟨hM, ?_⟩
    rw [hprod]
    exact (Int.modEq_and_modEq_iff_modEq_mul hcop).mp
      ⟨hnD.trans hD.symm, hnd.trans hd.symm⟩

noncomputable def residueMass (X g k : ℕ) (R : ℤ → Prop) : ℝ := by
  classical
  exact ∑ n ∈ supportInterval X, tent X n *
    (if R n ∧ (n % (g : ℤ)).toNat ∈ localAssignmentResidues g k then (1 : ℝ) else 0)

theorem subsetMass_eq_residueMass {P : Finset ℕ} {g k X : ℕ}
    (hg : Squarefree g) (hP : g.primeFactors ⊆ P) (R : ℤ → Prop) :
    subsetMass P k X R g.primeFactors = residueMass X g k R := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  have hiff : g.primeFactors ⊆ badPrimes P k n ↔
      (n % (g : ℤ)).toNat ∈ localAssignmentResidues g k := by
    rw [residue_mem_localAssignmentResidues_iff n hg]
    constructor
    · intro h p hp
      exact (Finset.mem_filter.mp (h hp)).2
    · intro h p hp
      exact Finset.mem_filter.mpr ⟨hP hp, h p hp⟩
  simp only [hiff]

/-- The overlap with the varying coordinate is removed by an equality;
there is no signed inequality in this step. -/
theorem residueMass_mul_eq {g u v d k i X : ℕ}
    (hg : Squarefree g) (hguv : g = u * v) (hud : u ∣ d) (hi : i < k)
    (R : ℤ → Prop) (hR : ∀ n, R n → Int.ModEq (d : ℤ) n (i : ℤ)) :
    residueMass X g k R = residueMass X v k R := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : R n
  · simp only [h, true_and, residue_allowed_mul_iff n hg hguv hud hi (hR n h)]
  · simp [h]

noncomputable def classMass (X v a : ℕ) (R : ℤ → Prop) : ℝ := by
  classical
  exact ∑ n ∈ supportInterval X,
    tent X n * (if R n ∧ (n % (v : ℤ)).toNat = a then (1 : ℝ) else 0)

theorem residueMass_eq_sum_classMass (X v k : ℕ) (R : ℤ → Prop) :
    residueMass X v k R = ∑ a ∈ localAssignmentResidues v k, classMass X v a R := by
  classical
  unfold residueMass classMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.mul_sum]
  congr 1
  by_cases hR : R n <;> simp [hR]

end Erdos387Proof.IntegerSieveResidues
