import MerLeanExperiment.CutoffFourier
import MerLeanExperiment.DiskDensity

open MeasureTheory
open scoped FourierTransform Convolution

namespace DiskDiscrepancy

theorem coe_areaBackground (M r : ℝ) (x : Plane) :
    (areaBackground M r x : ℂ) =
      ((fun y : Plane ↦ (boxDensity M y : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] diskIndicator r) x := by
  rw [areaBackground, ← integral_complex_ofReal]
  simp only [convolution_def, ContinuousLinearMap.mul_apply', Complex.ofReal_mul, coe_diskDensity]

theorem cutoffSignal_eq_count_sub_background (P : Finset Plane) (M r : ℝ) (x : Plane) :
    cutoffSignal P M r x =
      (((pointCount (↑P : Set Plane) x r : ℝ) - areaBackground M r x : ℝ) : ℂ) := by
  rw [← sum_diskDensity_eq_count P r x]
  simp only [Complex.ofReal_sub, Complex.ofReal_sum, coe_diskDensity, coe_areaBackground, cutoffSignal]

theorem norm_cutoffSignal (P : Finset Plane) (M r : ℝ) (x : Plane) :
    ‖cutoffSignal P M r x‖ = |(pointCount (↑P : Set Plane) x r : ℝ) - areaBackground M r x| := by
  rw [cutoffSignal_eq_count_sub_background, Complex.norm_real, Real.norm_eq_abs]

theorem norm_cutoffSignal_le (P : Finset Plane) (M : ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Plane) :
    ‖cutoffSignal P M r x‖ ≤ P.card + Real.pi * r ^ 2 := by
  have hcNat : pointCount (↑P : Set Plane) x r ≤ P.card := by
    simpa only [pointCount, Set.ncard_coe_finset] using Set.ncard_le_ncard (s := diskPoints (↑P : Set Plane) x r)
      (t := (↑P : Set Plane)) (fun _ hp ↦ hp.1) P.finite_toSet
  have hc : (pointCount (↑P : Set Plane) x r : ℝ) ≤ P.card := by exact_mod_cast hcNat
  rw [norm_cutoffSignal]
  have hb0 := areaBackground_nonneg M r x
  have hb := areaBackground_le_area M hr x
  have hc0 : (0 : ℝ) ≤ pointCount (↑P : Set Plane) x r := Nat.cast_nonneg _
  apply abs_le.mpr
  constructor <;> nlinarith [Real.pi_pos, sq_nonneg r, (Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card)]

theorem memLp_two_of_integrable_bounded {f : Plane → ℂ} (hf : Integrable f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have h := hf.norm.mul_bdd (c := C) hf.aestronglyMeasurable.norm
    (Filter.Eventually.of_forall fun x ↦ by simpa only [norm_norm] using hC x)
  simpa only [pow_two] using h

theorem memLp_cutoffSignal (P : Finset Plane) (M : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    MemLp (cutoffSignal P M r) 2 :=
  memLp_two_of_integrable_bounded (integrable_cutoffSignal P M r)
    (norm_cutoffSignal_le P M hr)

theorem cutoffSignal_interior {S : Set Plane} (hS : Admissible S) {M R r : ℝ} {x : Plane}
    (hx : x ∈ coordinateBox (M - R)) (hrR : r ≤ R) (hr : 0 ≤ r) :
    ‖cutoffSignal (cutoffPoints S hS M) M r x‖ = discrepancy S x r := by
  rw [norm_cutoffSignal, areaBackground_eq_area_of_interior hx hrR hr]
  unfold pointCount
  rw [cutoff_diskPoints_eq hS hx hrR]
  rfl

theorem areaBackground_exterior {M R r : ℝ} {x : Plane}
    (hx : x ∉ coordinateBox (M + R)) (hrR : r ≤ R) : areaBackground M r x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : y ∈ coordinateBox M
  · have hd : ¬dist y x ≤ r := by
      intro hd
      have hy' : y ∈ coordinateBox ((M + R) - R) := by simpa using hy
      exact hx (disk_subset_coordinateBox hy' hrR (by simpa [dist_comm] using hd))
    simp [diskDensity_sub, hd]
  · simp [boxDensity, hy]

theorem cutoffSignal_exterior {S : Set Plane} (hS : Admissible S) {M R r : ℝ} {x : Plane}
    (hx : x ∉ coordinateBox (M + R)) (hrR : r ≤ R) :
    cutoffSignal (cutoffPoints S hS M) M r x = 0 := by
  have hc : pointCount (↑(cutoffPoints S hS M) : Set Plane) x r = 0 := by
    have he : diskPoints (↑(cutoffPoints S hS M) : Set Plane) x r = ∅ := by
      ext y
      simp only [diskPoints, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hy hd ↦ no_cutoff_point_near_exterior hS hx hrR hy hd
    simp [pointCount, he]
  rw [cutoffSignal_eq_count_sub_background, hc, areaBackground_exterior hx hrR]
  norm_num

/-- Classical Plancherel applied to the actual finite-count/area cutoff signal. -/
theorem cutoffSignal_plancherel (P : Finset Plane) (M : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ ξ : Plane, ‖(𝓕 (cutoffSignal P M r) : Plane → ℂ) ξ‖ ^ 2) =
      ∫ x : Plane, ‖cutoffSignal P M r x‖ ^ 2 :=
  integral_norm_sq_fourier_of_integrable_memLp_two (integrable_cutoffSignal P M r)
    (memLp_cutoffSignal P M hr)

end DiskDiscrepancy
