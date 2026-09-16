import Erdos387Proof.IntegerClassFourier

/-! Exact zero/nonzero Fourier decomposition of a sifted integer class.
The nonzero remainder is an explicit Fourier sum, not an assumed error. -/

namespace Erdos387Proof.MediumResidueFourier

open Erdos387 IntegerSieveResidues IntegerClassFourier TentFourier
open scoped BigOperators

noncomputable def nonzeroSum (X q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
    ZMod.stdAddChar (-h * a) * TentFourier.coefficient X q h

theorem progressionMass_eq_zero_add_nonzero {X q : ℕ} [NeZero q]
    (hX : 0 < X) (a : ZMod q) :
    progressionMass X q a = (3 * (X : ℝ) + 1) / q + (nonzeroSum X q a).re := by
  classical
  have h := progressionMass_eq_fourier X q a
  rw [← Finset.add_sum_erase (Finset.univ : Finset (ZMod q))
    (fun h => ZMod.stdAddChar (-h * a) * TentFourier.coefficient X q h)
    (Finset.mem_univ 0)] at h
  simp only [neg_zero, zero_mul, AddChar.map_zero_eq_one, one_mul,
    coefficient_zero hX] at h
  have hr := congrArg Complex.re h
  have hz : (3 * (X : ℂ) + 1) / (q : ℂ) =
      (((3 * (X : ℝ) + 1) / (q : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hz] at hr
  simpa only [Complex.add_re, Complex.ofReal_re, nonzeroSum] using hr

noncomputable def residueRemainder (X Q v k b : ℕ) [NeZero Q] [NeZero v]
    (hcop : Nat.Coprime Q v) : ℝ :=
  ∑ a ∈ localAssignmentResidues v k,
    (nonzeroSum X (Q * v) (simultaneousResidue hcop b a : ZMod (Q * v))).re

/-- Summing all canonical allowed residues gives the exact local
multiplicity on the zero coefficient. -/
theorem residueMass_modEq_eq_main_add {X Q v k b : ℕ} [NeZero Q] [NeZero v]
    (hX : 0 < X) (hv : Squarefree v) (hcop : Nat.Coprime Q v)
    (hlarge : ∀ p ∈ v.primeFactors, k < p) :
    residueMass X v k (fun n => Int.ModEq (Q : ℤ) n (b : ℤ)) =
      (k : ℝ) ^ v.primeFactors.card * ((3 * (X : ℝ) + 1) / (Q * v : ℕ)) +
        residueRemainder X Q v k b hcop := by
  classical
  rw [residueMass_eq_sum_classMass]
  have heach (a : ℕ) (ha : a ∈ localAssignmentResidues v k) :
      classMass X v a (fun n => Int.ModEq (Q : ℤ) n (b : ℤ)) =
        (3 * (X : ℝ) + 1) / (Q * v : ℕ) +
          (nonzeroSum X (Q * v) (simultaneousResidue hcop b a : ZMod (Q * v))).re := by
    rw [classMass_eq_progressionMass X Q v a b hcop
      ((ConstrainedSieveResidues.mem_localAssignmentResidues_iff hv).mp ha).1]
    exact progressionMass_eq_zero_add_nonzero hX _
  rw [Finset.sum_congr rfl heach, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, card_localAssignmentResidues hlarge,
    Nat.cast_pow, residueRemainder]

end Erdos387Proof.MediumResidueFourier
