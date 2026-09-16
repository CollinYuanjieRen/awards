import MerLeanExperiment.TranslatedGcd
import MerLeanExperiment.LcmCollision
import MerLeanExperiment.External.Erdos441

namespace Erdos441

theorem at_most_one_translated_shift {K : ℕ} (M N : ℕ) (hM : 2 ≤ M)
    (hN : 0 < N) (r ell : Fin K → ℤ) (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (a : Fin K → ℝ) (ha : ∀ i, 0 < a i)
    (hleft : ∀ i, a i * Real.sqrt (N : ℝ) < (shiftedPoint M r ell i : ℝ))
    (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤
      (shiftParityWeight (r i) (r j) : ℝ) * a i * a j)
    (A : Finset ℕ) (hA : LcmBounded N A) (h : ℤ) (hh : 0 ≤ h) :
    (Finset.univ.filter fun i => (shiftedPoint M r ell i + 2 * h).natAbs ∈ A ∧
      Nat.Coprime (shiftedPoint M r ell i + 2 * h).natAbs
        (shiftProductNat M r ell)).card ≤ 1 := by
  classical
  have hlow (i : Fin K) : a i * Real.sqrt (N : ℝ) <
      ((shiftedPoint M r ell i + 2 * h).natAbs : ℝ) := by
    have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
    calc
      _ < (shiftedPoint M r ell i : ℝ) := hleft i
      _ ≤ (shiftedPoint M r ell i + 2 * h : ℤ) := by push_cast; linarith
      _ ≤ ((shiftedPoint M r ell i + 2 * h).natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact le_abs_self _
  have hcollision (i j : Fin K) (hij : i < j)
      (hiA : (shiftedPoint M r ell i + 2 * h).natAbs ∈ A)
      (hjA : (shiftedPoint M r ell j + 2 * h).natAbs ∈ A)
      (hicop : Nat.Coprime (shiftedPoint M r ell i + 2 * h).natAbs
        (shiftProductNat M r ell)) : False := by
    have hg := translated_shift_gcd_bound M hM r ell hr hsize i j hij h hicop
    have hgamma : 0 < shiftParityWeight (r i) (r j) := by
      unfold shiftParityWeight
      split_ifs <;> norm_num
    have hgt := lcm_gt_of_separated_lower_bounds (N : ℝ) (a i) (a j)
      ((r j - r i).natAbs : ℝ) (shiftedPoint M r ell i + 2 * h).natAbs
      (shiftedPoint M r ell j + 2 * h).natAbs (shiftParityWeight (r i) (r j))
      (Nat.cast_pos.mpr hN) (ha i) (ha j) hgamma (hlow i) (hlow j)
      (by exact_mod_cast hg) (hsep i j hij)
    have hle := hA.2 _ hiA _ hjA
    exact (not_lt_of_ge (Nat.cast_le.mpr hle)) hgt
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hcollision i j hij hi'.1 hj'.1 hi'.2).elim
  · exact hij
  · exact (hcollision j i hij hj'.1 hi'.1 hj'.2).elim

end Erdos441

#print axioms Erdos441.at_most_one_translated_shift
