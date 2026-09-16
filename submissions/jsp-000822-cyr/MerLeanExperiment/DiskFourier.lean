import MerLeanExperiment.AngularComplexIntegral
import MerLeanExperiment.DiskModel
import Mathlib.Analysis.Fourier.FourierTransform

open MeasureTheory
open scoped FourierTransform Real

namespace DiskDiscrepancy

/-- The actual complex-valued indicator of the closed disk centred at the origin. -/
noncomputable def diskIndicator (r : ℝ) : Plane → ℂ :=
  (Metric.closedBall (0 : Plane) r).indicator (fun _ ↦ 1)

/-- The closed-disk indicator is integrable for every real radius. -/
theorem integrable_diskIndicator (r : ℝ) : Integrable (diskIndicator r) := by
  unfold diskIndicator
  apply (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
  exact integrableOn_const
    ((isCompact_closedBall (0 : Plane) r).measure_ne_top)

/-- At zero frequency the disk transform is its area. -/
theorem fourier_diskIndicator_zero {r : ℝ} (hr : 0 ≤ r) :
    𝓕 (diskIndicator r) (0 : Plane) = ((Real.pi * r ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, one_smul]
  rw [diskIndicator, integral_indicator Metric.isClosed_closedBall.measurableSet]
  rw [MeasureTheory.integral_const]
  rw [measureReal_restrict_apply_univ, measureReal_def,
    EuclideanSpace.volume_closedBall_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal Real.pi_nonneg]
  rw [Complex.real_smul]
  push_cast
  ring

end DiskDiscrepancy
