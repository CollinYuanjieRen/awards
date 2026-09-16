import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Real
open MeasureTheory intervalIntegral Set Filter

namespace DiskDiscrepancy

/-- The normalized angular integral defining the order-zero Bessel kernel. -/
noncomputable def angularKernel (t : ℝ) : ℝ :=
  1 / (2 * Real.pi) *
    ∫ θ in (-Real.pi)..Real.pi, Real.cos (t * Real.sin θ)

/-- The angular integral representing the first derivative of `angularKernel`. -/
noncomputable def angularKernelDeriv (t : ℝ) : ℝ :=
  1 / (2 * Real.pi) *
    ∫ θ in (-Real.pi)..Real.pi,
      -Real.sin θ * Real.sin (t * Real.sin θ)

/-- The angular integral representing the second derivative of `angularKernel`. -/
noncomputable def angularKernelDeriv2 (t : ℝ) : ℝ :=
  1 / (2 * Real.pi) *
    ∫ θ in (-Real.pi)..Real.pi,
      -(Real.sin θ) ^ 2 * Real.cos (t * Real.sin θ)

/-- Differentiation under the angular integral gives the first derivative. -/
theorem hasDerivAt_angularKernel (t : ℝ) :
    HasDerivAt angularKernel (angularKernelDeriv t) t := by
  let F : ℝ → ℝ → ℝ := fun x θ ↦ Real.cos (x * Real.sin θ)
  let F' : ℝ → ℝ → ℝ := fun x θ ↦ -Real.sin θ * Real.sin (x * Real.sin θ)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : ℝ ↦ (1 : ℝ))
    (μ := volume)
    (x₀ := t) (s := Set.univ) (a := -Real.pi) (b := Real.pi)
    univ_mem
    (Filter.Eventually.of_forall fun x ↦
      (by fun_prop : Continuous (F x)).aestronglyMeasurable)
    (by exact (by fun_prop : Continuous (F t)).intervalIntegrable _ _)
    (by exact (by fun_prop : Continuous (F' t)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun θ _ x _ ↦ by
      dsimp [F']
      rw [abs_mul]
      calc
        |-Real.sin θ| * |Real.sin (x * Real.sin θ)| ≤ 1 * 1 :=
          mul_le_mul (by simpa using Real.abs_sin_le_one θ)
            (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num)
    (continuous_const.intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun θ _ x _ ↦ by
      dsimp [F, F']
      change HasDerivAt (fun y : ℝ ↦ Real.cos (y * Real.sin θ)) _ x
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_cos (x * Real.sin θ)).comp x
          ((hasDerivAt_id x).mul_const (Real.sin θ)))
  change HasDerivAt
    (fun y : ℝ ↦ 1 / (2 * Real.pi) *
      ∫ θ in (-Real.pi)..Real.pi, Real.cos (y * Real.sin θ))
    (1 / (2 * Real.pi) * ∫ θ in (-Real.pi)..Real.pi,
      -Real.sin θ * Real.sin (t * Real.sin θ)) t
  simpa only [F, F'] using (h.2.const_mul (1 / (2 * Real.pi)))

/-- Differentiation under the angular integral gives the second derivative. -/
theorem hasDerivAt_angularKernelDeriv (t : ℝ) :
    HasDerivAt angularKernelDeriv (angularKernelDeriv2 t) t := by
  let F : ℝ → ℝ → ℝ := fun x θ ↦ -Real.sin θ * Real.sin (x * Real.sin θ)
  let F' : ℝ → ℝ → ℝ := fun x θ ↦
    -(Real.sin θ) ^ 2 * Real.cos (x * Real.sin θ)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : ℝ ↦ (1 : ℝ))
    (μ := volume)
    (x₀ := t) (s := Set.univ) (a := -Real.pi) (b := Real.pi)
    univ_mem
    (Filter.Eventually.of_forall fun x ↦
      (by fun_prop : Continuous (F x)).aestronglyMeasurable)
    (by exact (by fun_prop : Continuous (F t)).intervalIntegrable _ _)
    (by exact (by fun_prop : Continuous (F' t)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun θ _ x _ ↦ by
      dsimp [F']
      rw [abs_mul]
      have hs := Real.abs_sin_le_one θ
      have hc := Real.abs_cos_le_one (x * Real.sin θ)
      rw [abs_neg, abs_pow]
      calc
        |Real.sin θ| ^ 2 * |Real.cos (x * Real.sin θ)| ≤ 1 ^ 2 * 1 :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hs 2) hc
            (abs_nonneg _) (by positivity)
        _ = 1 := by norm_num)
    (continuous_const.intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun θ _ x _ ↦ by
      dsimp [F, F']
      have hh := ((Real.hasDerivAt_sin (x * Real.sin θ)).comp x
        ((hasDerivAt_id x).mul_const (Real.sin θ))).mul_const (-Real.sin θ)
      have hcoef : Real.cos (x * Real.sin θ) * (1 * Real.sin θ) *
          (-Real.sin θ) = -(Real.sin θ) ^ 2 *
            Real.cos (x * Real.sin θ) := by ring
      simpa [Function.comp_def, mul_comm] using hh.congr_deriv hcoef)
  change HasDerivAt
    (fun y : ℝ ↦ 1 / (2 * Real.pi) *
      ∫ θ in (-Real.pi)..Real.pi,
        -Real.sin θ * Real.sin (y * Real.sin θ))
    (1 / (2 * Real.pi) * ∫ θ in (-Real.pi)..Real.pi,
      -(Real.sin θ) ^ 2 * Real.cos (t * Real.sin θ)) t
  simpa only [F, F'] using (h.2.const_mul (1 / (2 * Real.pi)))

/-- The angular kernel is continuous. -/
theorem continuous_angularKernel : Continuous angularKernel :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_angularKernel t).continuousAt

/-- The first angular derivative is continuous. -/
theorem continuous_angularKernelDeriv : Continuous angularKernelDeriv :=
  continuous_iff_continuousAt.2 fun t ↦
    (hasDerivAt_angularKernelDeriv t).continuousAt

/-- The explicit second angular derivative is continuous. -/
theorem continuous_angularKernelDeriv2 : Continuous angularKernelDeriv2 := by
  rw [show angularKernelDeriv2 = fun t : ℝ ↦
      1 / (2 * Real.pi) *
        ∫ θ in (-Real.pi)..Real.pi,
          -(Real.sin θ) ^ 2 * Real.cos (t * Real.sin θ) from rfl]
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

/-- The normalized angular kernel has absolute value at most one. -/
theorem abs_angularKernel_le_one (t : ℝ) : |angularKernel t| ≤ 1 := by
  rw [angularKernel, abs_mul]
  have hint :
      |∫ θ in (-Real.pi)..Real.pi, Real.cos (t * Real.sin θ)| ≤
        2 * Real.pi := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun θ : ℝ ↦ Real.cos (t * Real.sin θ))
      (a := -Real.pi) (b := Real.pi) (C := 1)
      (fun θ _ ↦ Real.abs_cos_le_one _)
    calc
      |∫ θ in (-Real.pi)..Real.pi, Real.cos (t * Real.sin θ)| =
          ‖∫ θ in (-Real.pi)..Real.pi, Real.cos (t * Real.sin θ)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ 1 * |Real.pi - -Real.pi| := h
      _ = 2 * Real.pi := by
        rw [abs_of_pos (by linarith [Real.pi_pos])]
        ring
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc
    1 / (2 * Real.pi) *
        |∫ θ in (-Real.pi)..Real.pi, Real.cos (t * Real.sin θ)|
        ≤ 1 / (2 * Real.pi) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 1 := by field_simp

/-- The first angular derivative has absolute value at most one. -/
theorem abs_angularKernelDeriv_le_one (t : ℝ) :
    |angularKernelDeriv t| ≤ 1 := by
  rw [angularKernelDeriv, abs_mul]
  have hint :
      |∫ θ in (-Real.pi)..Real.pi,
          -Real.sin θ * Real.sin (t * Real.sin θ)| ≤ 2 * Real.pi := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun θ : ℝ ↦ -Real.sin θ * Real.sin (t * Real.sin θ))
      (a := -Real.pi) (b := Real.pi) (C := 1)
      (fun θ _ ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul (by simpa using Real.abs_sin_le_one θ)
          (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)).trans_eq
            (by norm_num))
    calc
      |∫ θ in (-Real.pi)..Real.pi,
          -Real.sin θ * Real.sin (t * Real.sin θ)| =
          ‖∫ θ in (-Real.pi)..Real.pi,
            -Real.sin θ * Real.sin (t * Real.sin θ)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ 1 * |Real.pi - -Real.pi| := h
      _ = 2 * Real.pi := by
        rw [abs_of_pos (by linarith [Real.pi_pos])]
        ring
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc
    1 / (2 * Real.pi) *
        |∫ θ in (-Real.pi)..Real.pi,
          -Real.sin θ * Real.sin (t * Real.sin θ)|
        ≤ 1 / (2 * Real.pi) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 1 := by field_simp

/-- On the unit interval the angular kernel is bounded below by one half. -/
theorem one_half_le_angularKernel {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 : ℝ) / 2 ≤ angularKernel t := by
  have hpoint : ∀ θ : ℝ, (1 : ℝ) / 2 ≤
      Real.cos (t * Real.sin θ) := by
    intro θ
    have ha : |t * Real.sin θ| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht0]
      nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ)]
    have hsq : (t * Real.sin θ) ^ 2 ≤ 1 := by
      nlinarith [sq_abs (t * Real.sin θ),
        mul_self_le_mul_self (abs_nonneg (t * Real.sin θ)) ha]
    exact le_trans (by linarith)
      Real.one_sub_sq_div_two_le_cos
  have hc : Continuous fun θ : ℝ ↦ Real.cos (t * Real.sin θ) := by fun_prop
  have hi : (∫ θ in (-Real.pi)..Real.pi, (1 : ℝ) / 2) ≤
      ∫ θ in (-Real.pi)..Real.pi, Real.cos (t * Real.sin θ) :=
    intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
      (fun θ _ ↦ hpoint θ)
  simp only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul] at hi
  have heq : (Real.pi + Real.pi) * ((1 : ℝ) / 2) = Real.pi := by ring
  rw [heq] at hi
  rw [angularKernel]
  calc
    (1 : ℝ) / 2 = 1 / (2 * Real.pi) * Real.pi := by field_simp
    _ ≤ 1 / (2 * Real.pi) *
        (∫ θ in (-Real.pi)..Real.pi, Real.cos (t * Real.sin θ)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)

/-- The angular integral satisfies the order-zero Bessel differential equation. -/
theorem angularKernel_ode (t : ℝ) :
    t * angularKernelDeriv2 t + angularKernelDeriv t +
      t * angularKernel t = 0 := by
  let f : ℝ → ℝ := fun θ ↦
    Real.cos θ * Real.sin (t * Real.sin θ)
  let f' : ℝ → ℝ := fun θ ↦
    -Real.sin θ * Real.sin (t * Real.sin θ) +
      t * (Real.cos θ) ^ 2 * Real.cos (t * Real.sin θ)
  have hfderiv : ∀ θ : ℝ, HasDerivAt f (f' θ) θ := by
    intro θ
    have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (t * Real.sin x))
        (Real.cos (t * Real.sin θ) * (t * Real.cos θ)) θ := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sin (t * Real.sin θ)).comp θ
          ((Real.hasDerivAt_sin θ).const_mul t)
    dsimp [f, f']
    have hh := (Real.hasDerivAt_cos θ).mul hsin
    exact hh.congr_deriv (by ring)
  have hf'int : IntervalIntegrable f' volume (-Real.pi) Real.pi := by
    exact (by fun_prop : Continuous f').intervalIntegrable _ _
  have hzero : (∫ θ in (-Real.pi)..Real.pi, f' θ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ ↦ hfderiv θ) hf'int]
    simp [f]
  have hi0 : IntervalIntegrable
      (fun θ : ℝ ↦ Real.cos (t * Real.sin θ)) volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous fun θ : ℝ ↦
        Real.cos (t * Real.sin θ)).intervalIntegrable _ _
  have hi1 : IntervalIntegrable
      (fun θ : ℝ ↦ -Real.sin θ * Real.sin (t * Real.sin θ)) volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous fun θ : ℝ ↦
        -Real.sin θ * Real.sin (t * Real.sin θ)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun θ : ℝ ↦ -(Real.sin θ) ^ 2 * Real.cos (t * Real.sin θ)) volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous fun θ : ℝ ↦
        -(Real.sin θ) ^ 2 * Real.cos (t * Real.sin θ)).intervalIntegrable _ _
  have hcombine :
      t * (∫ θ in (-Real.pi)..Real.pi,
          -(Real.sin θ) ^ 2 * Real.cos (t * Real.sin θ)) +
        (∫ θ in (-Real.pi)..Real.pi,
          -Real.sin θ * Real.sin (t * Real.sin θ)) +
        t * (∫ θ in (-Real.pi)..Real.pi,
          Real.cos (t * Real.sin θ)) =
        ∫ θ in (-Real.pi)..Real.pi, f' θ := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hi2.const_mul t) hi1,
      ← intervalIntegral.integral_add ((hi2.const_mul t).add hi1)
        (hi0.const_mul t)]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [f']
    have htrig : (Real.cos θ) ^ 2 = 1 - (Real.sin θ) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [htrig]
    ring
  rw [angularKernelDeriv2, angularKernelDeriv, angularKernel]
  linear_combination (1 / (2 * Real.pi)) * (hcombine.trans hzero)

end DiskDiscrepancy
