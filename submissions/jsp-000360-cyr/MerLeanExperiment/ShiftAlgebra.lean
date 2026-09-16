import MerLeanExperiment.ShiftDefinitions

namespace Erdos441

theorem shift_factor_mul_difference {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (i j : Fin K) (hd : r j - r i ≠ 0) (hsize : 2 * (r j - r i).natAbs ≤ M) :
    (r j - r i) * shiftFactor M r ell i j =
      shiftedPoint M r ell j - shiftedPoint M r ell i := by
  have heq := (factorial_linear_spec M (r j - r i) hd hsize (ell i)).1
  unfold shiftFactor shiftedPoint
  calc
    _ = ((r j - r i) * ((M.factorial : ℤ) / (r j - r i))) *
        (ell j - ell i) + (r j - r i) := by ring
    _ = _ := by rw [heq]; ring

theorem shift_points_injective {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M) :
    Function.Injective (shiftedPoint M r ell) := by
  intro i j hpoint
  by_contra hij
  have hd : r j - r i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hr h).symm)
  have hdpos : 0 < (r j - r i).natAbs := Int.natAbs_pos.mpr hd
  have hsmall : (r j - r i).natAbs < M := by
    have hs := hsize i j hij
    omega
  have hdiv : (M.factorial : ℤ) ∣ r j - r i := by
    refine ⟨ell i - ell j, ?_⟩
    unfold shiftedPoint at hpoint
    nlinarith
  have hle : M.factorial ≤ (r j - r i).natAbs :=
    Nat.le_of_dvd hdpos (Int.natCast_dvd.mp hdiv)
  have hMF := Nat.self_le_factorial M
  omega

theorem shift_factor_ne_zero {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ)
    (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (i j : Fin K) (hij : i ≠ j) : shiftFactor M r ell i j ≠ 0 := by
  intro hz
  have hd : r j - r i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hr h).symm)
  have heq := shift_factor_mul_difference M r ell i j hd (hsize i j hij)
  rw [hz, mul_zero] at heq
  have hp : shiftedPoint M r ell j = shiftedPoint M r ell i := sub_eq_zero.mp heq.symm
  exact hij ((shift_points_injective M r ell hr hsize) hp).symm

end Erdos441

#print axioms Erdos441.shift_factor_mul_difference
#print axioms Erdos441.shift_points_injective
#print axioms Erdos441.shift_factor_ne_zero
