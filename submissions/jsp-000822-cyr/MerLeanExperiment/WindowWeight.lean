import MerLeanExperiment.WindowFourier

open MeasureTheory
open scoped FourierTransform Convolution

namespace DiskDiscrepancy

/-- The real indicator of the same interval used by `intervalWindow`. -/
noncomputable def realIntervalWindow (a : ℝ) : ℝ → ℝ :=
  (Set.Icc (-a / 2) (a / 2)).indicator (fun _ ↦ 1)

/-- A normalized convolution of actual interval indicators. -/
noncomputable def windowWeight (a x : ℝ) : ℝ :=
  a⁻¹ * ∫ t : ℝ, realIntervalWindow a t * realIntervalWindow a (x - t)

theorem realIntervalWindow_nonneg (a t : ℝ) : 0 ≤ realIntervalWindow a t := by
  by_cases ht : t ∈ Set.Icc (-a / 2) (a / 2) <;> simp [realIntervalWindow, ht]

theorem realIntervalWindow_le_one (a t : ℝ) : realIntervalWindow a t ≤ 1 := by
  by_cases ht : t ∈ Set.Icc (-a / 2) (a / 2) <;> simp [realIntervalWindow, ht]

theorem measurable_realIntervalWindow (a : ℝ) : Measurable (realIntervalWindow a) :=
  measurable_const.indicator measurableSet_Icc

theorem integrable_realIntervalWindow (a : ℝ) : Integrable (realIntervalWindow a) := by
  unfold realIntervalWindow
  exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem coe_realIntervalWindow (a t : ℝ) :
    (realIntervalWindow a t : ℂ) = intervalWindow a t := by
  by_cases ht : t ∈ Set.Icc (-a / 2) (a / 2) <;>
    simp [realIntervalWindow, intervalWindow, ht]

theorem integral_realIntervalWindow {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, realIntervalWindow a t) = a := by
  unfold realIntervalWindow
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a / 2 ≤ a / 2)]
  simp
  ring

theorem integrable_windowWeight_integrand (a x : ℝ) :
    Integrable (fun t : ℝ ↦ realIntervalWindow a t * realIntervalWindow a (x - t)) := by
  apply (integrable_realIntervalWindow a).mul_bdd (c := 1)
    ((measurable_realIntervalWindow a).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  filter_upwards [] with t
  simpa only [Function.comp_apply, Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg (realIntervalWindow_nonneg a (x - t))] using
    realIntervalWindow_le_one a (x - t)

theorem windowWeight_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ windowWeight a x := by
  apply mul_nonneg (inv_nonneg.mpr ha.le)
  exact integral_nonneg fun t ↦
    mul_nonneg (realIntervalWindow_nonneg a t) (realIntervalWindow_nonneg a (x - t))

theorem windowWeight_le_one {a : ℝ} (ha : 0 < a) (x : ℝ) : windowWeight a x ≤ 1 := by
  have hi : (∫ t : ℝ, realIntervalWindow a t * realIntervalWindow a (x - t)) ≤ a := by
    calc
     _ ≤ ∫ t : ℝ, realIntervalWindow a t := by
      apply integral_mono (integrable_windowWeight_integrand a x) (integrable_realIntervalWindow a)
      intro t
      exact mul_le_of_le_one_right (realIntervalWindow_nonneg a t)
        (realIntervalWindow_le_one a (x - t))
     _ = a := integral_realIntervalWindow ha
  calc
    windowWeight a x ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr ha.le)
    _ = 1 := inv_mul_cancel₀ ha.ne'

theorem windowWeight_eq_zero_of_lt_abs {a x : ℝ} (hx : a < |x|) :
    windowWeight a x = 0 := by
  have hi (t : ℝ) : realIntervalWindow a t * realIntervalWindow a (x - t) = 0 := by
    by_cases ht : t ∈ Set.Icc (-a / 2) (a / 2)
    · by_cases hs : x - t ∈ Set.Icc (-a / 2) (a / 2)
      · have ht' : |t| ≤ a / 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        have hs' : |x - t| ≤ a / 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
        have hsum := abs_add_le t (x - t)
        have heq : t + (x - t) = x := by ring
        rw [heq] at hsum
        exfalso
        linarith
      · simp [realIntervalWindow, hs]
    · simp [realIntervalWindow, ht]
  simp [windowWeight, hi]

theorem coe_windowWeight (a : ℝ) :
    (fun x : ℝ ↦ (windowWeight a x : ℂ)) =
      (a : ℂ)⁻¹ • (intervalWindow a ⋆[ContinuousLinearMap.mul ℂ ℂ] intervalWindow a) := by
  funext x
  simp only [windowWeight, Complex.ofReal_mul, Complex.ofReal_inv, Pi.smul_apply,
    smul_eq_mul, convolution_def, ContinuousLinearMap.mul_apply']
  congr 1
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Complex.ofReal_mul, coe_realIntervalWindow]

theorem integrable_windowWeight (a : ℝ) : Integrable (windowWeight a) := by
  have h := (integrable_realIntervalWindow a).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (integrable_realIntervalWindow a)
  change Integrable (fun x : ℝ ↦ a⁻¹ * ∫ t : ℝ, realIntervalWindow a t * realIntervalWindow a (x - t))
  simpa only [convolution_def, ContinuousLinearMap.mul_apply'] using h.const_mul a⁻¹

/-- The normalized interval convolution has the positive sinc-squared Fourier transform. -/
theorem fourier_windowWeight {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕 (fun t : ℝ ↦ (windowWeight a t : ℂ)) x = (sincKernel a x : ℂ) := by
  have hsmul (c : ℂ) (f : ℝ → ℂ) : 𝓕 (c • f) x = c * 𝓕 f x := by
    simp only [Real.fourier_eq', Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm _ c]
    exact integral_const_mul c _
  rw [coe_windowWeight, hsmul]
  rw [Real.fourier_mul_convolution_eq (integrable_intervalWindow a) (integrable_intervalWindow a),
    fourier_intervalWindow ha]
  simp only [sincKernel, Complex.ofReal_mul, Complex.ofReal_pow]
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  field_simp [haC]

end DiskDiscrepancy
