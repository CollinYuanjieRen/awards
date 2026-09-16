import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

namespace ReciprocalSquares

/-- Two multiples of a sufficiently large common divisor cannot both be
close to the same integer unless they coincide. -/
theorem nearby_multiples_eq (h M₁ M₂ P H : ℤ)
    (h₁ : P ∣ M₁) (h₂ : P ∣ M₂)
    (hnear₁ : |h - M₁| ≤ H) (hnear₂ : |h - M₂| ≤ H)
    (hscale : 2 * H < P) : M₁ = M₂ := by
  by_contra hne
  have hlower : P ≤ |M₁ - M₂| :=
    Int.le_abs_of_dvd (sub_ne_zero.mpr hne) (dvd_sub h₁ h₂)
  have hupper : |M₁ - M₂| ≤ |h - M₁| + |h - M₂| := by
    calc
      |M₁ - M₂| = |(M₁ - h) + (h - M₂)| := by congr 1; ring
      _ ≤ |M₁ - h| + |h - M₂| := abs_add_le _ _
      _ = |h - M₁| + |h - M₂| := by rw [abs_sub_comm M₁ h]
  omega

/-- A factor missing from a nearby integer forces separation from every
multiple of the corresponding test denominator. Coprimality is unnecessary. -/
theorem missing_factor_separation (h M b P H : ℤ)
    (hPM : P ∣ M) (hb : ¬ b ∣ M)
    (hnear : |h - M| ≤ H) (hscale : 2 * H ≤ P) (z : ℤ) :
    P ≤ 2 * |h - b * P * z| := by
  have hnz : M - b * P * z ≠ 0 := by
    intro heq
    apply hb
    refine ⟨P * z, ?_⟩
    nlinarith
  have hdiv : P ∣ M - b * P * z := by
    apply dvd_sub hPM
    exact ⟨b * z, by ring⟩
  have hlower := Int.le_abs_of_dvd hnz hdiv
  have hupper : |M - b * P * z| ≤ |h - M| + |h - b * P * z| := by
    calc
      |M - b * P * z| = |(M - h) + (h - b * P * z)| := by congr 1; ring
      _ ≤ |M - h| + |h - b * P * z| := abs_add_le _ _
      _ = |h - M| + |h - b * P * z| := by rw [abs_sub_comm M h]
  omega

end ReciprocalSquares
