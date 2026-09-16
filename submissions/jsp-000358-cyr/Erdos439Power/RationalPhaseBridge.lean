import Erdos439Power.PolynomialPhase
import Erdos439Power.PeriodicMainTerm
import Erdos439Power.Vendor.ErdosProblems.Erdos439.PowerSums

open scoped BigOperators ComplexConjugate Polynomial

namespace Erdos439Power

noncomputable section

/-- The normalized-power polynomial character is the corresponding real
exponential phase. -/
theorem polynomialPhase_normalizedPowerPolynomial
    (q a k L n : ℕ) [NeZero q] :
    polynomialPhase q a (Erdos439.PowerDecay.normalizedPowerPolynomial k L)
        (n : ZMod q) =
      realPhase (2 * Real.pi * ((a : ℝ) / q) * Erdos439.normalizedPower k L n) := by
  rw [polynomialPhase]
  have heval :
      (Erdos439.PowerDecay.normalizedPowerPolynomial k L).eval₂
          (Int.castRingHom (ZMod q)) (n : ZMod q) =
        (Erdos439.normalizedPower k L n : ZMod q) := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.eval_natCast_map,
      Erdos439.PowerDecay.eval_normalizedPowerPolynomial]
    simp
  rw [heval]
  have harg : (a : ZMod q) * (Erdos439.normalizedPower k L n : ZMod q) =
      (((a * Erdos439.normalizedPower k L n : ℕ) : ℤ) : ZMod q) := by
    norm_num
  rw [harg]
  rw [ZMod.stdAddChar_coe]
  unfold realPhase
  congr 1
  push_cast
  field_simp

/-- The conjugated polynomial character pulled back to the naturals is
periodic with its modulus. -/
theorem periodic_conj_polynomialPhase (q a : ℕ) [NeZero q] (P : ℤ[X]) :
    Function.Periodic
      (fun n : ℕ => conj (polynomialPhase q a P (n : ZMod q))) q := by
  intro n
  simp only [Nat.cast_add, ZMod.natCast_self, add_zero]

/-- The period mean of a pulled-back conjugated polynomial character is its
complete `ZMod` expectation. -/
theorem periodicMean_conj_polynomialPhase (q a : ℕ) [NeZero q] (P : ℤ[X]) :
    periodicMean (fun n : ℕ => conj (polynomialPhase q a P (n : ZMod q))) q =
      conj (𝔼 x : ZMod q, polynomialPhase q a P x) := by
  rw [← expect_conj]
  unfold periodicMean
  rw [Fintype.expect_eq_sum_div_card]
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  rw [hcard]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  let base : Fin q ≃ ZMod q :=
    { toFun := fun i => (i : ZMod q)
      invFun := fun h => (⟨h.val, h.val_lt⟩ : Fin q)
      left_inv := fun i => Fin.ext (by simp [ZMod.val_natCast_of_lt i.isLt])
      right_inv := fun h => ZMod.natCast_zmod_val h }
  exact Fintype.sum_equiv base _ _ (fun _ => rfl)

theorem norm_periodicMean_conj_polynomialPhase
    (q a : ℕ) [NeZero q] (P : ℤ[X]) :
    ‖periodicMean (fun n : ℕ => conj (polynomialPhase q a P (n : ZMod q))) q‖ =
      ‖𝔼 x : ZMod q, polynomialPhase q a P x‖ := by
  rw [periodicMean_conj_polynomialPhase, Complex.norm_conj]

/-- The integral Fourier character is the corresponding negative real
phase. -/
theorem phase_neg_eq_realPhase (T t n : ℕ) (hT : 0 < T) :
    Erdos438.Fourier.phase T (-(t : ℤ)) (n : ℤ) =
      realPhase (-2 * Real.pi * ((t : ℝ) / T) * n) := by
  unfold Erdos438.Fourier.phase realPhase
  congr 1
  push_cast
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp [hT0]

private theorem conj_realPhase (x : ℝ) : conj (realPhase x) = realPhase (-x) := by
  unfold realPhase
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp

/-- Exact major-arc factorization into a slowly varying real phase and a
periodic rational polynomial character. -/
theorem phase_normalizedPower_factorization
    (T t q a k L n : ℕ) (hT : 0 < T) [NeZero q] :
    let α : ℝ := (t : ℝ) / T
    let β : ℝ := -2 * Real.pi * (α - (a : ℝ) / q)
    Erdos438.Fourier.phase T (-(t : ℤ))
        (Erdos439.normalizedPower k L n : ℤ) =
      realPhase (β * Erdos439.normalizedPower k L n) *
        conj (polynomialPhase q a
          (Erdos439.PowerDecay.normalizedPowerPolynomial k L) (n : ZMod q)) := by
  dsimp only
  rw [phase_neg_eq_realPhase _ _ _ hT,
    polynomialPhase_normalizedPowerPolynomial, conj_realPhase,
    ← realPhase_add]
  congr 1
  ring

/-- Every polynomial character modulo one is trivial. -/
theorem conj_polynomialPhase_one (a n : ℕ) (P : ℤ[X]) :
    conj (polynomialPhase 1 a P (n : ZMod 1)) = 1 := by
  have hx : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  have ha : (a : ZMod 1) = 0 := Subsingleton.elim _ _
  rw [hx]
  simp [polynomialPhase, ha]

end

end Erdos439Power
