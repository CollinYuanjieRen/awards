import MerLeanExperiment.SpectralLower

open MeasureTheory
open scoped FourierTransform ComplexConjugate

namespace DiskDiscrepancy

/-- A closed coordinate square in the genuine Euclidean plane. -/
def coordinateBox (a : ℝ) : Set Plane := {x | ∀ i, |x i| ≤ a}

theorem isClosed_coordinateBox (a : ℝ) : IsClosed (coordinateBox a) := by
  have heq : coordinateBox a = ⋂ i : Fin 2, {x : Plane | |x i| ≤ a} := by
    ext x
    simp [coordinateBox]
  rw [heq]
  exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const

theorem norm_sq_le_of_mem_coordinateBox {a : ℝ} {x : Plane} (hx : x ∈ coordinateBox a) :
    ‖x‖ ^ 2 ≤ 2 * a ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h0 := pow_le_pow_left₀ (abs_nonneg (x 0)) (hx 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg (x 1)) (hx 1) 2
  simpa only [sq_abs, two_mul] using add_le_add h0 h1

theorem isCompact_coordinateBox (a : ℝ) : IsCompact (coordinateBox a) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_coordinateBox a, ?_⟩
  apply (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 2 * |a| + 1)).subset
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq := norm_sq_le_of_mem_coordinateBox hx
  nlinarith [sq_abs a, abs_nonneg a, norm_nonneg x]

theorem norm_le_six_of_mem_frequencyBox {x : Plane} (hx : x ∈ coordinateBox 4) : ‖x‖ ≤ 6 := by
  have hsq := norm_sq_le_of_mem_coordinateBox hx
  norm_num at hsq
  nlinarith [norm_nonneg x]

theorem planeWindow_eq_zero_off_box {a : ℝ} {x : Plane} (hx : x ∉ coordinateBox a) :
    planeWindow a x = 0 := by
  apply planeWindow_eq_zero
  simpa only [coordinateBox, Set.mem_ofPred_eq, not_forall, not_le] using hx

/-- The discrepancy spectrum has definite energy in one fixed frequency square. -/
theorem fixed_box_discrepancy_energy_lower (P : Finset Plane)
    {g : Plane → ℝ} (hg : Integrable g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    8 * P.card ≤ ∫ ξ in coordinateBox 4,
      ‖atomicFourier P ξ - (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ‖ ^ 2 := by
  let F : Plane → ℝ := fun ξ ↦
    ‖atomicFourier P ξ - (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ‖ ^ 2
  have hF0 (ξ : Plane) : 0 ≤ F ξ := sq_nonneg _
  have hgC : Integrable (fun y : Plane ↦ (g y : ℂ)) := hg.ofReal
  have hFcont : Continuous F :=
    ((continuous_atomicFourier P).sub (continuous_classicalFourier hgC)).norm.pow 2
  have hFi : IntegrableOn F (coordinateBox 4) :=
    hFcont.continuousOn.integrableOn_compact (isCompact_coordinateBox 4)
  have hWFi : IntegrableOn (fun ξ ↦ planeWindow 4 ξ * F ξ) (coordinateBox 4) := by
    apply hFi.bdd_mul (c := 1) (integrable_planeWindow 4).aestronglyMeasurable.restrict
    exact Filter.Eventually.of_forall fun ξ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (planeWindow_nonneg (by norm_num) ξ)]
      exact planeWindow_le_one (by norm_num) ξ
  have heq : (∫ ξ : Plane, planeWindow 4 ξ * F ξ) =
      ∫ ξ in coordinateBox 4, planeWindow 4 ξ * F ξ := by
    rw [← integral_indicator (isClosed_coordinateBox 4).measurableSet]
    apply integral_congr_ae
    filter_upwards [] with ξ
    by_cases hξ : ξ ∈ coordinateBox 4
    · simp [hξ]
    · simp [hξ, planeWindow_eq_zero_off_box hξ]
  have hlow := weighted_discrepancy_energy_lower (by norm_num : (0 : ℝ) < 4) P hg hg0 hg1
  norm_num only [show (4 : ℝ) ^ 2 - 8 = 8 by norm_num] at hlow
  calc
    8 * P.card ≤ ∫ ξ : Plane, planeWindow 4 ξ * F ξ := hlow
    _ = ∫ ξ in coordinateBox 4, planeWindow 4 ξ * F ξ := heq
    _ ≤ ∫ ξ in coordinateBox 4, F ξ :=
      integral_mono hWFi hFi (fun ξ ↦ mul_le_of_le_one_left (hF0 ξ)
        (planeWindow_le_one (by norm_num) ξ))

end DiskDiscrepancy
