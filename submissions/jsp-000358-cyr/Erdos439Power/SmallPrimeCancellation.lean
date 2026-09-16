import Mathlib

open scoped BigOperators ComplexConjugate

namespace Erdos439Power

noncomputable section

/-- Cancellation from a nontrivial additive translation of a function on a
finite cyclic group. -/
theorem sum_stdAddChar_eq_zero_of_shift {q : ℕ} [NeZero q]
    (F : ZMod q → ZMod q) (a h : ZMod q)
    (hshift : ∀ x, F (x + h) = F x + h) (hah : a * h ≠ 0) :
    ∑ x : ZMod q, ZMod.stdAddChar (a * F x) = 0 := by
  let S : ℂ := ∑ x : ZMod q, ZMod.stdAddChar (a * F x)
  have htranslate : (∑ x : ZMod q, ZMod.stdAddChar (a * F (x + h))) = S :=
    Fintype.sum_bijective _ (AddGroup.addRight_bijective h) _ _ fun _ => rfl
  have hchar : ZMod.stdAddChar (a * h) ≠ 1 := by
    intro heq
    have heq0 : ZMod.stdAddChar (a * h) = ZMod.stdAddChar (0 : ZMod q) := by
      simpa using heq
    exact hah (ZMod.injective_stdAddChar heq0)
  have hmul' : S * ZMod.stdAddChar (a * h) = S := by
    calc
      S * ZMod.stdAddChar (a * h) =
          ∑ x : ZMod q, ZMod.stdAddChar (a * F x) * ZMod.stdAddChar (a * h) := by
        rw [Finset.sum_mul]
      _ = ∑ x : ZMod q, ZMod.stdAddChar (a * F (x + h)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hshift, mul_add, AddChar.map_add_eq_mul]
      _ = S := htranslate
  have hmul : ZMod.stdAddChar (a * h) * S = S := by simpa [mul_comm] using hmul'
  exact eq_zero_of_mul_eq_self_left hchar hmul

/-- A small prime dividing both the modulus and the non-linear coefficient
forces complete cancellation of the associated polynomial character sum. -/
theorem smallPrime_polynomial_character_sum_eq_zero
    (q p a L : ℕ) [NeZero q] (C : ℤ) (Q : Polynomial ℤ)
    (hq : 0 < q) (hp : Nat.Prime p) (hpq : p ∣ q) (hpL : p ∣ L)
    (haq : Nat.Coprime a q) :
    (∑ x : ZMod q, ZMod.stdAddChar
      ((a : ZMod q) * Polynomial.eval₂ (Int.castRingHom (ZMod q)) x
        (Polynomial.X + Q * Polynomial.C C * Polynomial.C (L : ℤ)))) = 0 := by
  let h : ZMod q := (q / p : ℕ)
  let Qq : Polynomial (ZMod q) := Q.map (Int.castRingHom (ZMod q))
  let F : ZMod q → ZMod q := fun x => x + Qq.eval x * (C : ZMod q) * (L : ZMod q)
  have hp_le_q : p ≤ q := Nat.le_of_dvd hq hpq
  have hhpos : 0 < q / p := Nat.div_pos hp_le_q hp.pos
  have hpqh : p * (q / p) = q := Nat.mul_div_cancel' hpq
  have hph : (p : ZMod q) * h = 0 := by
    dsimp [h]
    rw [← Nat.cast_mul, hpqh, ZMod.natCast_self]
  have hLh : (L : ZMod q) * h = 0 := by
    obtain ⟨k, hk⟩ := hpL
    subst L
    push_cast
    calc
      (p : ZMod q) * k * h = k * (p * h) := by ring
      _ = 0 := by rw [hph, mul_zero]
  have hshift : ∀ x, F (x + h) = F x + h := by
    intro x
    have hdvd := Polynomial.sub_dvd_eval_sub (x + h) x Qq
    rcases hdvd with ⟨t, ht⟩
    have heval : Qq.eval (x + h) = Qq.eval x + h * t := by
      rw [show x + h - x = h by abel] at ht
      linear_combination ht
    dsimp [F]
    rw [heval]
    calc
      x + h + (Qq.eval x + h * t) * (C : ZMod q) * L =
          x + h + Qq.eval x * C * L + C * (L * h) * t := by ring
      _ = x + Qq.eval x * C * L + h := by rw [hLh]; ring
  have hah : (a : ZMod q) * h ≠ 0 := by
    dsimp [h]
    rw [← Nat.cast_mul]
    rw [ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hcancel : p ∣ a := by
      have : p * (q / p) ∣ a * (q / p) := by
        rw [hpqh]
        exact hdvd
      exact (Nat.mul_dvd_mul_iff_right hhpos).mp this
    have hpa : Nat.Coprime p a := (haq.of_dvd_right hpq).symm
    exact (hp.coprime_iff_not_dvd.mp hpa) hcancel
  have hPeval (x : ZMod q) :
      Polynomial.eval₂ (Int.castRingHom (ZMod q)) x
          (Polynomial.X + Q * Polynomial.C C * Polynomial.C (L : ℤ)) = F x := by
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_C]
    rw [← Polynomial.eval_map]
    dsimp [F, Qq]
    norm_cast
  have hsum := sum_stdAddChar_eq_zero_of_shift F (a : ZMod q) h hshift hah
  simpa only [hPeval] using hsum

end


end Erdos439Power
