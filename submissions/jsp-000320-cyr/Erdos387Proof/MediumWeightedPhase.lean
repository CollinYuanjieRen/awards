import Erdos387Proof.MediumReciprocalPhase
import Erdos387Proof.MediumWeightedKloosterman
import Erdos387Proof.MediumFactorGeometry

/-!
# Weighted medium reciprocal phase

The exact Fourier summand on the coprime varying-factor class is rewritten
as the tent weight times the zero-extended inverse Kloosterman coefficient.
The definition below retains the full coprimality mask, so the subsequent
interval sum is over every integer in the interval.
-/

namespace Erdos387Proof.MediumWeightedPhase

open Erdos387
open MediumReciprocalPhase FourierVariation
open scoped BigOperators

/-- The inverse coefficient after `d=u*t`. -/
noncomputable def reciprocalCoefficient
    (Q u gamma i : ℕ) (h : ℤ) : ZMod Q :=
  (((-h) * ((gamma : ℤ) - i) : ℤ) : ZMod Q) * (u : ZMod Q)⁻¹

/-- The canonical Bézout inverse of `u*t` is the product of the two
individual inverses modulo `Q`. -/
theorem gcdB_mul_eq_inv_mul_inv
    (Q u t : ℕ) [NeZero Q]
    (hcop : Nat.Coprime Q (u * t)) :
    (Nat.gcdB Q (u * t) : ZMod Q) =
      (u : ZMod Q)⁻¹ * (t : ZMod Q)⁻¹ := by
  have hbez : (1 : ℤ) =
      (Q : ℤ) * Nat.gcdA Q (u * t) +
        (u * t : ℤ) * Nat.gcdB Q (u * t) := by
    simpa [hcop.gcd_eq_one] using Nat.gcd_eq_gcd_ab Q (u * t)
  have hmul : ((u * t : ℕ) : ZMod Q) *
      (Nat.gcdB Q (u * t) : ZMod Q) = 1 := by
    calc
      ((u * t : ℕ) : ZMod Q) * (Nat.gcdB Q (u * t) : ZMod Q) =
          (((Q : ℤ) * Nat.gcdA Q (u * t) +
            (u * t : ℤ) * Nat.gcdB Q (u * t) : ℤ) : ZMod Q) := by
        push_cast
        simp
      _ = 1 := by rw [← hbez]; simp
  have hinv : ((u * t : ℕ) : ZMod Q)⁻¹ =
      (Nat.gcdB Q (u * t) : ZMod Q) :=
    ZMod.inv_eq_of_mul_eq_one Q _ _ hmul
  have huQ : Nat.Coprime u Q :=
    Nat.Coprime.of_dvd_left (dvd_mul_right u t) hcop.symm
  have htQ : Nat.Coprime t Q :=
    Nat.Coprime.of_dvd_left (dvd_mul_left t u) hcop.symm
  have hcandidate : ((u * t : ℕ) : ZMod Q) *
      ((u : ZMod Q)⁻¹ * (t : ZMod Q)⁻¹) = 1 := by
    push_cast
    calc
      (u : ZMod Q) * (t : ZMod Q) *
          ((u : ZMod Q)⁻¹ * (t : ZMod Q)⁻¹) =
          ((u : ZMod Q) * (u : ZMod Q)⁻¹) *
            ((t : ZMod Q) * (t : ZMod Q)⁻¹) := by ring
      _ = 1 := by rw [ZMod.coe_mul_inv_eq_one u huQ,
        ZMod.coe_mul_inv_eq_one t htQ, one_mul]
  rw [← hinv]
  exact ZMod.inv_eq_of_mul_eq_one Q _ _ hcandidate

/-- Exact equality of one coprime Fourier summand with the weighted
zero-extended Kloosterman coefficient. -/
theorem fourierSummand_eq_weightedCoefficient
    (X Q u t gamma i : ℕ) [NeZero Q] [NeZero u] [NeZero t]
    (huQ : Nat.Coprime u Q) (htQ : Nat.Coprime t Q) (h : ℤ) :
    let hcop : Nat.Coprime Q (u * t) :=
      huQ.symm.mul_right htQ.symm
    ZMod.stdAddChar
        (-(h : ZMod (Q * (u * t))) *
          (simultaneousResidue hcop gamma i : ZMod (Q * (u * t)))) *
        TentFourier.coefficient X (Q * (u * t)) (h : ZMod (Q * (u * t))) =
      tentWeight X h (-i) (Q * (u * t) : ℕ)⁻¹ *
        Kloosterman.coefficient Q (reciprocalCoefficient Q u gamma i h)
          (t : ZMod Q) := by
  dsimp only
  let hcop : Nat.Coprime Q (u * t) := huQ.symm.mul_right htQ.symm
  have htUnit : IsUnit (t : ZMod Q) :=
    (ZMod.isUnit_iff_coprime t Q).2 htQ
  rw [Kloosterman.coefficient, if_pos htUnit]
  rw [SimultaneousFourier.stdAddChar_mul_simultaneousResidue_reciprocity
    hcop gamma i (-(h : ZMod (Q * (u * t))))]
  rw [tentWeight_inv_eq]
  have hfirst :
      (ZMod.chineseRemainder hcop (-(h : ZMod (Q * (u * t))))).1 =
        (-h : ZMod Q) := by
    simp [ZMod.chineseRemainder, ZMod.castHom_apply]
  rw [hfirst, gcdB_mul_eq_inv_mul_inv Q u t hcop]
  unfold reciprocalCoefficient
  have hrecip :
      ZMod.stdAddChar
          ((-h : ZMod Q) * ((gamma : ZMod Q) - (i : ZMod Q)) *
            ((u : ZMod Q)⁻¹ * (t : ZMod Q)⁻¹)) =
        ZMod.stdAddChar
          ((((-h) * ((gamma : ℤ) - i) : ℤ) : ZMod Q) *
            (u : ZMod Q)⁻¹ * (t : ZMod Q)⁻¹) := by
    congr 1
    push_cast
    ring
  have hsmall :
      ZMod.stdAddChar ((-h : ZMod (Q * (u * t))) *
          (i : ZMod (Q * (u * t)))) =
        ZMod.stdAddChar ((h : ZMod (Q * (u * t))) *
          ((-i : ℤ) : ZMod (Q * (u * t)))) := by
    congr 1
    push_cast
    ring
  rw [hrecip, hsmall]
  ring

/-- A proof-carrying masked summand.  It is zero off the actual coprime
class and uses the exact simultaneous CRT residue on that class. -/
noncomputable def maskedFourierSummand
    (X Q u gamma i : ℕ) [NeZero Q] [NeZero u]
    (huQ : Nat.Coprime u Q) (h : ℤ) (t : ℕ) (ht : 0 < t) : ℂ := by
  letI : NeZero t := ⟨ht.ne'⟩
  by_cases htQ : Nat.Coprime t Q
  · let hcop : Nat.Coprime Q (u * t) := huQ.symm.mul_right htQ.symm
    exact ZMod.stdAddChar
        (-(h : ZMod (Q * (u * t))) *
          (simultaneousResidue hcop gamma i : ZMod (Q * (u * t)))) *
        TentFourier.coefficient X (Q * (u * t)) (h : ZMod (Q * (u * t)))
  · exact 0

set_option linter.style.haveILetI false in
/-- The proof-carrying masked summand is definitionally independent of the
coprimality proof and equals the zero-extended Kloosterman expression. -/
theorem maskedFourierSummand_eq
    (X Q u gamma i : ℕ) [NeZero Q] [NeZero u]
    (huQ : Nat.Coprime u Q) (h : ℤ) (t : ℕ) (ht : 0 < t) :
    maskedFourierSummand X Q u gamma i huQ h t ht =
      tentWeight X h (-i) (Q * u * t : ℕ)⁻¹ *
        Kloosterman.coefficient Q (reciprocalCoefficient Q u gamma i h)
          (t : ZMod Q) := by
  letI : NeZero t := ⟨ht.ne'⟩
  by_cases htQ : Nat.Coprime t Q
  · rw [maskedFourierSummand]
    simp only [dif_pos htQ]
    simpa only [Nat.mul_assoc] using
      fourierSummand_eq_weightedCoefficient X Q u t gamma i huQ htQ h
  · rw [maskedFourierSummand]
    simp only [dif_neg htQ]
    have hnot : ¬IsUnit (t : ZMod Q) := fun hunit =>
      htQ ((ZMod.isUnit_iff_coprime t Q).mp hunit)
    rw [Kloosterman.coefficient, if_neg hnot, mul_zero]

/-- The squarefree CRT coordinate of the actual inverse coefficient is the
local coefficient audited in `MediumReciprocalPhase`. -/
theorem reciprocalCoefficient_localCoordinate
    (M q u gamma i : ℕ) [NeZero M] [NeZero q]
    (hcop : Nat.Coprime M q) (hu : Nat.Coprime u (M * q)) (h : ℤ) :
    (ZMod.chineseRemainder hcop
        (reciprocalCoefficient (M * q) u gamma i h)).2 *
        (Nat.gcdA M q : ZMod q) =
      localKloostermanCoefficient M q u (-h) ((gamma : ℤ) - i) := by
  have huUnit : IsUnit (u : ZMod (M * q)) :=
    (ZMod.isUnit_iff_coprime u (M * q)).2 hu
  have hinv := Kloosterman.chineseRemainder_inv_of_isUnit
    hcop (u : ZMod (M * q)) huUnit
  unfold reciprocalCoefficient localKloostermanCoefficient inverseCoefficient
  simp only [map_mul, Prod.snd_mul]
  rw [hinv]
  simp [ZMod.chineseRemainder, ZMod.castHom_apply]

/-- The actual coefficient entering the weighted theorem has local gcd at
most `v*|h|`.  Cancellation is used only on `D`; no unit assumption modulo
`v` is introduced. -/
theorem gcd_reciprocalCoefficient_le
    (M D v u gamma i : ℕ) [NeZero M] [NeZero (D * v)]
    (hcop : Nat.Coprime M (D * v))
    (hu : Nat.Coprime u (M * (D * v)))
    (h : ℤ) (hh : h ≠ 0)
    (hdelta : Int.gcd ((gamma : ℤ) - i) D = 1)
    (hD : 0 < D) :
    Nat.gcd
        (((ZMod.chineseRemainder hcop
          (reciprocalCoefficient (M * (D * v)) u gamma i h)).2 *
            (Nat.gcdA M (D * v) : ZMod (D * v))).val)
        (D * v) ≤ v * h.natAbs := by
  rw [reciprocalCoefficient_localCoordinate M (D * v) u gamma i hcop hu h]
  have huLocal : Nat.Coprime u (D * v) :=
    Nat.Coprime.of_dvd_right (dvd_mul_left (D * v) M) hu
  simpa only [Int.natAbs_neg] using
    gcd_localKloostermanCoefficient_le M D v u (-h) ((gamma : ℤ) - i)
      hD (neg_ne_zero.mpr hh) hdelta huLocal hcop

/-- The actual medium factor geometry supplies the reciprocal scale in the
weighted Kloosterman estimate.  The local gcd remains the explicit one in
the compiled squarefree bound; `MediumReciprocalPhase` bounds it by
`v*|h|` for the actual certificate coefficient. -/
theorem norm_sum_maskedFourierSummand_le
    (B X M D v u medium : ℕ)
    [NeZero M] [NeZero (D * v)] [NeZero u]
    (hB : 0 < B) (hX : 0 < X) (hD : 0 < D)
    (hM : 0 < M) (hv : 0 < v) (hm : 0 < medium)
    (hcop : Nat.Coprime M (D * v))
    (hsq : Squarefree (D * v))
    (hlarge : ∀ p ∈ (D * v).primeFactors, 2 < p)
    (huQ : Nat.Coprime u (M * (D * v)))
    (gamma i : ℕ) (h : ℤ) (H : ℝ)
    (hH : 0 ≤ H) (hh : |(h : ℝ)| ≤ H) (hi : |-(i : ℤ)| ≤ (X : ℤ))
    (L : ℕ) :
    ‖∑ r ∈ Finset.range L,
      maskedFourierSummand X (M * (D * v)) u gamma i huQ h
        (MediumFactorWindow.lower B X D medium / u + r + 1)
          (Nat.zero_lt_succ _)‖ ≤
      (8 * ((6 * (B : ℝ)) / (M * v : ℕ)) +
          128 * H * ((6 * (B : ℝ)) / (M * v : ℕ))^2) *
        (((L / (M * (D * v)) + 1 : ℕ) : ℝ) *
          PeriodicCompletion.Kloosterman.fixedMulSquarefreeIntervalBound
            M (D * v) hcop
              (reciprocalCoefficient (M * (D * v)) u gamma i h)) := by
  have hbound :
      (X : ℝ) /
          (M * (D * v) * u *
            (MediumFactorWindow.lower B X D medium / u + 1) : ℕ) ≤
        (6 * (B : ℝ)) / (M * v : ℕ) := by
    simpa only [Nat.mul_assoc] using
      MediumFactorGeometry.X_div_first_modulus_le
      (B := B) (X := X) (D := D) (M := M) (v := v) (u := u)
        (medium := medium) hB hD hM hv (NeZero.pos u) hm
  simp_rw [maskedFourierSummand_eq]
  apply MediumWeightedKloosterman.norm_sum_tentWeight_inverse_le
    X M (D * v) u (MediumFactorWindow.lower B X D medium / u) L
    hX (NeZero.pos u) hcop hsq hlarge
    (reciprocalCoefficient (M * (D * v)) u gamma i h) h (-i)
    ((6 * (B : ℝ)) / (M * v : ℕ)) H
  · positivity
  · exact hH
  · exact hh
  · exact hi
  · exact hbound

set_option maxHeartbeats 800000 in
/-- The weighted interval estimate with the squarefree gcd factor replaced
by the certificate loss `v*|h|`. -/
theorem norm_sum_maskedFourierSummand_le_gcd
    (B X M D v u medium : ℕ)
    [NeZero M] [NeZero (D * v)] [NeZero u]
    (hB : 0 < B) (hX : 0 < X) (hD : 0 < D)
    (hM : 0 < M) (hv : 0 < v) (hm : 0 < medium)
    (hcop : Nat.Coprime M (D * v))
    (hsq : Squarefree (D * v))
    (hlarge : ∀ p ∈ (D * v).primeFactors, 2 < p)
    (huQ : Nat.Coprime u (M * (D * v)))
    (gamma i : ℕ) (h : ℤ) (hh0 : h ≠ 0)
    (hdelta : Int.gcd ((gamma : ℤ) - i) D = 1)
    (H : ℝ) (hH : 0 ≤ H) (hh : |(h : ℝ)| ≤ H)
    (hi : |-(i : ℤ)| ≤ (X : ℤ)) (L : ℕ) :
    ‖∑ r ∈ Finset.range L,
      maskedFourierSummand X (M * (D * v)) u gamma i huQ h
        (MediumFactorWindow.lower B X D medium / u + r + 1)
          (Nat.zero_lt_succ _)‖ ≤
      (8 * ((6 * (B : ℝ)) / (M * v : ℕ)) +
          128 * H * ((6 * (B : ℝ)) / (M * v : ℕ))^2) *
        (((L / (M * (D * v)) + 1 : ℕ) : ℝ) *
          ((Real.log (M * (D * v) : ℕ) + 1) *
            ((4 : ℝ) ^ (D * v).primeFactors.card *
              Real.sqrt (D * v : ℝ) *
              Real.sqrt (v * h.natAbs : ℝ) * M))) := by
  have hraw := norm_sum_maskedFourierSummand_le B X M D v u medium
    hB hX hD hM hv hm hcop hsq hlarge huQ gamma i h H hH hh hi L
  apply hraw.trans
  unfold PeriodicCompletion.Kloosterman.fixedMulSquarefreeIntervalBound
  have hgcd := gcd_reciprocalCoefficient_le
    M D v u gamma i hcop huQ h hh0 hdelta hD
  have hgcdR :
      ((Nat.gcd
        (((ZMod.chineseRemainder hcop
          (reciprocalCoefficient (M * (D * v)) u gamma i h)).2 *
            (Nat.gcdA M (D * v) : ZMod (D * v))).val)
          (D * v) : ℕ) : ℝ) ≤ (v * h.natAbs : ℕ) := by
    exact_mod_cast hgcd
  have hmodulusOne : (1 : ℝ) ≤ (M * (D * v) : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (M * (D * v))))
  have hlog : 0 ≤ Real.log (M * (D * v) : ℕ) + 1 :=
    add_nonneg (Real.log_nonneg hmodulusOne) zero_le_one
  simp only [Nat.cast_mul]
  gcongr
  · simpa only [Nat.cast_mul] using hlog
  · simpa only [Nat.cast_mul] using hgcdR

end Erdos387Proof.MediumWeightedPhase
