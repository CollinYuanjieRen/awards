import Erdos439Power.CyclicWeyl
import Erdos439Power.Vendor.ErdosProblems.Erdos439.PowerSums
import Erdos439Power.SmallPrimeCancellation

open scoped BigOperators ComplexConjugate Polynomial

namespace Erdos439Power

noncomputable section

/-- The additive character associated to an integral polynomial modulo `q`. -/
def polynomialPhase (q a : ℕ) [NeZero q] (P : ℤ[X]) (x : ZMod q) : ℂ :=
  ZMod.stdAddChar
    ((a : ZMod q) * P.eval₂ (Int.castRingHom (ZMod q)) x)

@[simp] theorem norm_polynomialPhase (q a : ℕ) [NeZero q]
    (P : ℤ[X]) (x : ZMod q) :
    ‖polynomialPhase q a P x‖ = 1 := by
  simp [polynomialPhase]

/-- Multiplicative differencing of a polynomial phase is the phase of the
formal forward difference. -/
theorem cyclicDifference_polynomialPhase (q a : ℕ) [NeZero q]
    (P : ℤ[X]) (h : ZMod q) :
    cyclicDifference (polynomialPhase q a P) h =
      polynomialPhase q a
        (Erdos439.PowerDecay.polynomialShiftDifference (h.val : ℤ) P) := by
  funext x
  unfold cyclicDifference polynomialPhase
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Erdos439.PowerDecay.polynomialShiftDifference,
    Polynomial.eval₂_sub, Polynomial.eval₂_comp, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  have hh : (Int.castRingHom (ZMod q)) (h.val : ℤ) = h := by
    change ((h.val : ℤ) : ZMod q) = h
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hh]
  ring

private theorem sum_polynomialPhase_eq_zero_of_shift
    {q a : ℕ} [NeZero q] (P : ℤ[X]) (h c : ZMod q)
    (hshift : ∀ x : ZMod q,
      P.eval₂ (Int.castRingHom (ZMod q)) (x + h) =
        P.eval₂ (Int.castRingHom (ZMod q)) x + c)
    (hac : (a : ZMod q) * c ≠ 0) :
    ∑ x : ZMod q, polynomialPhase q a P x = 0 := by
  let F : ZMod q → ZMod q :=
    fun x => P.eval₂ (Int.castRingHom (ZMod q)) x
  let S : ℂ := ∑ x : ZMod q, polynomialPhase q a P x
  have htranslate : (∑ x : ZMod q, polynomialPhase q a P (x + h)) = S :=
    Fintype.sum_bijective _ (AddGroup.addRight_bijective h) _ _ fun _ => rfl
  have hchar : ZMod.stdAddChar ((a : ZMod q) * c) ≠ 1 := by
    intro heq
    have heq0 : ZMod.stdAddChar ((a : ZMod q) * c) =
        ZMod.stdAddChar (0 : ZMod q) := by simpa using heq
    exact hac (ZMod.injective_stdAddChar heq0)
  have hmul' : S * ZMod.stdAddChar ((a : ZMod q) * c) = S := by
    calc
      S * ZMod.stdAddChar ((a : ZMod q) * c) =
          ∑ x : ZMod q, polynomialPhase q a P x *
            ZMod.stdAddChar ((a : ZMod q) * c) := by
        rw [Finset.sum_mul]
      _ = ∑ x : ZMod q, polynomialPhase q a P (x + h) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [polynomialPhase, polynomialPhase, hshift, mul_add,
          AddChar.map_add_eq_mul]
      _ = S := htranslate
  have hmul : ZMod.stdAddChar ((a : ZMod q) * c) * S = S := by
    simpa [mul_comm] using hmul'
  exact eq_zero_of_mul_eq_self_left hchar hmul

/-- A genuinely linear polynomial phase has zero complete average whenever
its linear frequency is nonzero modulo the modulus. -/
theorem expect_polynomialPhase_eq_zero_of_natDegree_eq_one
    (q a : ℕ) [NeZero q] (P : ℤ[X])
    (hdegree : P.natDegree = 1)
    (hfrequency : (a : ZMod q) * (P.leadingCoeff : ZMod q) ≠ 0) :
    (𝔼 x : ZMod q, polynomialPhase q a P x) = 0 := by
  have hrepr : P = Polynomial.C P.leadingCoeff * Polynomial.X +
      Polynomial.C (P.coeff 0) := by
    have h := Polynomial.eq_X_add_C_of_natDegree_le_one hdegree.le
    simpa [Polynomial.leadingCoeff, hdegree] using h
  have hshift : ∀ x : ZMod q,
      P.eval₂ (Int.castRingHom (ZMod q)) (x + 1) =
        P.eval₂ (Int.castRingHom (ZMod q)) x +
          (P.leadingCoeff : ZMod q) := by
    intro x
    calc
      P.eval₂ (Int.castRingHom (ZMod q)) (x + 1) =
          (Polynomial.C P.leadingCoeff * Polynomial.X +
            Polynomial.C (P.coeff 0)).eval₂
              (Int.castRingHom (ZMod q)) (x + 1) :=
        congrArg (fun Q : ℤ[X] =>
          Q.eval₂ (Int.castRingHom (ZMod q)) (x + 1)) hrepr
      _ = (Polynomial.C P.leadingCoeff * Polynomial.X +
            Polynomial.C (P.coeff 0)).eval₂
              (Int.castRingHom (ZMod q)) x +
            (P.leadingCoeff : ZMod q) := by
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        change (P.leadingCoeff : ZMod q) * (x + 1) +
            (P.coeff 0 : ZMod q) =
          ((P.leadingCoeff : ZMod q) * x + (P.coeff 0 : ZMod q)) +
            (P.leadingCoeff : ZMod q)
        ring
      _ = P.eval₂ (Int.castRingHom (ZMod q)) x +
          (P.leadingCoeff : ZMod q) := by
        exact congrArg (fun z : ZMod q => z + (P.leadingCoeff : ZMod q))
          (congrArg (fun Q : ℤ[X] =>
            Q.eval₂ (Int.castRingHom (ZMod q)) x) hrepr).symm
  have hsum := sum_polynomialPhase_eq_zero_of_shift P 1
    (P.leadingCoeff : ZMod q) hshift hfrequency
  rw [Fintype.expect_eq_sum_div_card, hsum]
  simp

end

end Erdos439Power
