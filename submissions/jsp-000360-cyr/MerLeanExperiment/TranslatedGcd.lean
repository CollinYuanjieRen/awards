import MerLeanExperiment.CollisionDefinitions
import MerLeanExperiment.GcdCancellation
import MerLeanExperiment.ShiftAlgebra

namespace Erdos441

theorem translated_shift_gcd_bound {K : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (r ell : Fin K → ℤ) (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (i j : Fin K) (hij : i < j) (h : ℤ)
    (hcop : Nat.Coprime (shiftedPoint M r ell i + 2 * h).natAbs
      (shiftProductNat M r ell)) :
    shiftParityWeight (r i) (r j) *
      Nat.gcd (shiftedPoint M r ell i + 2 * h).natAbs
        (shiftedPoint M r ell j + 2 * h).natAbs ≤ (r j - r i).natAbs := by
  have hd : r j - r i ≠ 0 := sub_ne_zero.mpr (fun he => (ne_of_lt hij) (hr he).symm)
  have hdpos : 0 < (r j - r i).natAbs := Int.natAbs_pos.mpr hd
  have hfactor : shiftFactor M r ell i j ∣ shiftProduct M r ell := by
    unfold shiftProduct
    apply Finset.dvd_prod_of_mem (fun ij : Fin K × Fin K => shiftFactor M r ell ij.1 ij.2)
      (a := (i, j))
    simp [shiftPairs, hij]
  have hfactorNat : (shiftFactor M r ell i j).natAbs ∣ shiftProductNat M r ell := by
    obtain ⟨k, hk⟩ := hfactor
    refine ⟨k.natAbs, ?_⟩
    simp only [shiftProductNat, hk, Int.natAbs_mul]
  have hdiff : (shiftedPoint M r ell j + 2 * h) -
      (shiftedPoint M r ell i + 2 * h) =
      (r j - r i) * shiftFactor M r ell i j := by
    rw [shift_factor_mul_difference M r ell i j hd (hsize i j (ne_of_lt hij))]
    ring
  have hgd := gcd_dvd_difference_factor _ _ _ _ _ hdiff hfactorNat hcop
  by_cases hodd : Odd (r i) ∧ Odd (r j)
  · rw [shiftParityWeight, ite_eq_left hodd]
    have htwo : (2 : ℤ) ∣ (M.factorial : ℤ) := by
      exact_mod_cast Nat.dvd_factorial (by omega : 0 < 2) hM
    have hfact : Even (M.factorial : ℤ) := even_iff_two_dvd.mpr htwo
    have hpoint : Odd (shiftedPoint M r ell i + 2 * h) := by
      exact ((hfact.mul_right (ell i)).add_odd hodd.1).add_even (even_two.mul_right h)
    have hgodd : Odd (Nat.gcd (shiftedPoint M r ell i + 2 * h).natAbs
        (shiftedPoint M r ell j + 2 * h).natAbs) := by
      exact Nat.coprime_two_left.mp
        (hpoint.natAbs.coprime_two_left.of_dvd_right (Nat.gcd_dvd_left _ _))
    exact two_mul_le_of_odd_dvd_even _ _ hdpos hgodd (hodd.2.sub_odd hodd.1).natAbs hgd
  · rw [shiftParityWeight, ite_eq_right hodd, one_mul]
    exact Nat.le_of_dvd hdpos hgd

end Erdos441

#print axioms Erdos441.translated_shift_gcd_bound
