import MerLeanExperiment.BoxGeometry
import MerLeanExperiment.DiskFourier

open MeasureTheory
open scoped FourierTransform

namespace DiskDiscrepancy

noncomputable def diskDensity (r : ℝ) : Plane → ℝ :=
  (Metric.closedBall (0 : Plane) r).indicator (fun _ ↦ 1)

theorem diskDensity_nonneg (r : ℝ) (x : Plane) : 0 ≤ diskDensity r x := by
  by_cases h : x ∈ Metric.closedBall (0 : Plane) r <;> simp [diskDensity, h]

theorem diskDensity_le_one (r : ℝ) (x : Plane) : diskDensity r x ≤ 1 := by
  by_cases h : x ∈ Metric.closedBall (0 : Plane) r <;> simp [diskDensity, h]

theorem coe_diskDensity (r : ℝ) (x : Plane) : (diskDensity r x : ℂ) = diskIndicator r x := by
  by_cases h : x ∈ Metric.closedBall (0 : Plane) r <;> simp [diskDensity, diskIndicator, h]

theorem integrable_diskDensity (r : ℝ) : Integrable (diskDensity r) := by
  apply (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
  exact integrableOn_const ((isCompact_closedBall (0 : Plane) r).measure_ne_top)

theorem integral_diskDensity {r : ℝ} (hr : 0 ≤ r) :
    (∫ x : Plane, diskDensity r x) = Real.pi * r ^ 2 := by
  have h := fourier_diskIndicator_zero hr
  rw [Real.fourier_eq'] at h
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul] at h
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simpa only [coe_diskDensity] using h

theorem diskDensity_sub (r : ℝ) (x p : Plane) :
    diskDensity r (x - p) = if dist p x ≤ r then 1 else 0 := by
  classical
  simp only [diskDensity, Set.indicator_apply, Metric.mem_closedBall, dist_zero_right]
  rw [← dist_eq_norm, dist_comm x p]

theorem sum_diskDensity_eq_count (P : Finset Plane) (r : ℝ) (x : Plane) :
    (∑ p ∈ P, diskDensity r (x - p)) = (pointCount (↑P : Set Plane) x r : ℝ) := by
  classical
  have hset : diskPoints (↑P : Set Plane) x r = ↑(P.filter fun p ↦ dist p x ≤ r) := by
    ext p
    simp [diskPoints]
  simp_rw [diskDensity_sub]
  rw [pointCount, hset, Set.ncard_coe_finset, Finset.sum_boole]

noncomputable def areaBackground (M r : ℝ) (x : Plane) : ℝ :=
  ∫ y : Plane, boxDensity M y * diskDensity r (x - y)

theorem integrable_areaBackground_integrand (M r : ℝ) (x : Plane) :
    Integrable (fun y : Plane ↦ boxDensity M y * diskDensity r (x - y)) := by
  apply ((integrable_diskDensity r).comp_sub_left x).bdd_mul (c := 1)
    (integrable_boxDensity M).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (boxDensity_nonneg M y)] using boxDensity_le_one M y

theorem areaBackground_nonneg (M r : ℝ) (x : Plane) : 0 ≤ areaBackground M r x :=
  integral_nonneg fun y ↦ mul_nonneg (boxDensity_nonneg M y) (diskDensity_nonneg r (x - y))

theorem areaBackground_le_area (M : ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Plane) :
    areaBackground M r x ≤ Real.pi * r ^ 2 := by
  calc
    _ ≤ ∫ y : Plane, diskDensity r (x - y) :=
      integral_mono (integrable_areaBackground_integrand M r x)
        ((integrable_diskDensity r).comp_sub_left x) (fun y ↦
          mul_le_of_le_one_left (diskDensity_nonneg r (x - y)) (boxDensity_le_one M y))
    _ = ∫ y : Plane, diskDensity r y := integral_sub_left_eq_self _ volume x
    _ = _ := integral_diskDensity hr

theorem areaBackground_eq_area_of_interior {M R r : ℝ} {x : Plane}
    (hx : x ∈ coordinateBox (M - R)) (hrR : r ≤ R) (hr : 0 ≤ r) :
    areaBackground M r x = Real.pi * r ^ 2 := by
  calc
    _ = ∫ y : Plane, diskDensity r (x - y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hd : dist y x ≤ r
      · have hy : y ∈ coordinateBox M := disk_subset_coordinateBox hx hrR hd
        simp only [boxDensity, Set.indicator_of_mem hy, one_mul]
      · simp only [diskDensity_sub, ite_eq_right hd, mul_zero]
    _ = ∫ y : Plane, diskDensity r y := integral_sub_left_eq_self _ volume x
    _ = _ := integral_diskDensity hr

end DiskDiscrepancy
