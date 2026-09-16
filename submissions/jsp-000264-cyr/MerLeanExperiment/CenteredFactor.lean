import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace ReciprocalSquares

/-- Characteristic function of a centered Bernoulli variable. The angle is in
radians; the arithmetic application uses `t = 2 * π * h / d`. -/
noncomputable def centeredFactor (p t : ℝ) : ℂ :=
  ((1 - p : ℝ) : ℂ) * Complex.exp (((-p * t : ℝ) : ℂ) * Complex.I) +
    (p : ℂ) * Complex.exp ((((1 - p) * t : ℝ) : ℂ) * Complex.I)

@[simp] theorem centeredFactor_zero (p : ℝ) : centeredFactor p 0 = 1 := by
  simp [centeredFactor]

theorem norm_centeredFactor_le_one (p t : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    ‖centeredFactor p t‖ ≤ 1 := by
  calc
    ‖centeredFactor p t‖ ≤
        ‖((1 - p : ℝ) : ℂ) * Complex.exp (((-p * t : ℝ) : ℂ) * Complex.I)‖ +
          ‖(p : ℂ) * Complex.exp ((((1 - p) * t : ℝ) : ℂ) * Complex.I)‖ :=
      norm_add_le _ _
    _ = 1 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg hp,
        abs_of_nonneg (sub_nonneg.mpr hp')]
      ring

theorem centeredFactor_factor (p t : ℝ) :
    centeredFactor p t =
      Complex.exp (((-p * t : ℝ) : ℂ) * Complex.I) *
        (((1 - p : ℝ) : ℂ) +
          (p : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) := by
  have he : Complex.exp ((((1 - p) * t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-p * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((t : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold centeredFactor
  rw [he]
  ring

theorem norm_centeredFactor_sq (p t : ℝ) :
    ‖centeredFactor p t‖ ^ 2 =
      1 - 2 * p * (1 - p) * (1 - Real.cos t) := by
  rw [centeredFactor_factor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.exp_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, mul_one, zero_add, add_zero,
    Real.exp_zero, one_mul]
  nlinarith [congrArg (fun x : ℝ => p ^ 2 * x) (Real.sin_sq_add_cos_sq t)]

/-- This Gaussian estimate is valid even outside the probability interval;
probability bounds are used later to make the exponent uniformly negative. -/
theorem norm_centeredFactor_le_exp (p t : ℝ) :
    ‖centeredFactor p t‖ ≤
      Real.exp (-p * (1 - p) * (1 - Real.cos t)) := by
  have hs := Real.add_one_le_exp (-2 * p * (1 - p) * (1 - Real.cos t))
  have he : Real.exp (-2 * p * (1 - p) * (1 - Real.cos t)) =
      Real.exp (-p * (1 - p) * (1 - Real.cos t)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hs
  have hn := norm_centeredFactor_sq p t
  have hp := Real.exp_pos (-p * (1 - p) * (1 - Real.cos t))
  nlinarith [norm_nonneg (centeredFactor p t)]

theorem centeredFactor_re (p t : ℝ) :
    (centeredFactor p t).re =
      (1 - p) * Real.cos (-p * t) + p * Real.cos ((1 - p) * t) := by
  simp only [centeredFactor, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re]

theorem centeredFactor_im (p t : ℝ) :
    (centeredFactor p t).im =
      (1 - p) * Real.sin (-p * t) + p * Real.sin ((1 - p) * t) := by
  simp only [centeredFactor, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im]

private theorem abs_mul_le_self (q t : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) :
    |q * t| ≤ |t| := by
  rw [abs_mul, abs_of_nonneg hq]
  nlinarith [abs_nonneg t]

/-- Centering cancels the linear imaginary term; the remaining bound is
cubic for every real angle. -/
theorem abs_im_centeredFactor_le_cube (p t : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |(centeredFactor p t).im| ≤ |t| ^ 3 / 6 := by
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hq1 : 1 - p ≤ 1 := by linarith
  have ha : |-p * t| ≤ |t| := by
    simpa only [neg_mul, abs_neg] using abs_mul_le_self p t hp0 hp1
  have hb := abs_mul_le_self (1 - p) t hq0 hq1
  have hsin : ∀ x : ℝ, |x| ≤ |t| → |Real.sin x - x| ≤ |t| ^ 3 / 6 := by
    intro x hx
    calc
      |Real.sin x - x| = |x - Real.sin x| := abs_sub_comm _ _
      _ ≤ |x| ^ 3 / 6 := Real.abs_sub_sin_le x
      _ ≤ |t| ^ 3 / 6 := by gcongr
  rw [centeredFactor_im]
  calc
    _ = |(1 - p) * (Real.sin (-p * t) - (-p * t)) +
        p * (Real.sin ((1 - p) * t) - (1 - p) * t)| := by congr 1; ring
    _ ≤ |(1 - p) * (Real.sin (-p * t) - (-p * t))| +
        |p * (Real.sin ((1 - p) * t) - (1 - p) * t)| := abs_add_le _ _
    _ = (1 - p) * |Real.sin (-p * t) - (-p * t)| +
        p * |Real.sin ((1 - p) * t) - (1 - p) * t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hp0]
    _ ≤ (1 - p) * (|t| ^ 3 / 6) + p * (|t| ^ 3 / 6) :=
      add_le_add (mul_le_mul_of_nonneg_left (hsin _ ha) hq0)
        (mul_le_mul_of_nonneg_left (hsin _ hb) hp0)
    _ = |t| ^ 3 / 6 := by ring

theorem half_le_centeredFactor_re (p t : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    (1 / 2 : ℝ) ≤ (centeredFactor p t).re := by
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hq1 : 1 - p ≤ 1 := by linarith
  have ha : |-p * t| ≤ 1 := by
    have := (abs_mul_le_self p t hp0 hp1).trans ht
    simpa only [neg_mul, abs_neg] using this
  have hb := (abs_mul_le_self (1 - p) t hq0 hq1).trans ht
  have hcos : ∀ x : ℝ, |x| ≤ 1 → (1 / 2 : ℝ) ≤ Real.cos x := by
    intro x hx
    have hsq : x ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by positivity : 0 ≤ 1 + |x|),
        sq_abs x]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  rw [centeredFactor_re]
  have hleft := mul_le_mul_of_nonneg_left (hcos _ ha) hq0
  have hright := mul_le_mul_of_nonneg_left (hcos _ hb) hp0
  linarith

end ReciprocalSquares
