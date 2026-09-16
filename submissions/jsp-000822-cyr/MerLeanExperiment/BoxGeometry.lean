import MerLeanExperiment.CoordinateBox

open MeasureTheory
open scoped FourierTransform

namespace DiskDiscrepancy

noncomputable def boxDensity (a : ℝ) : Plane → ℝ :=
  (coordinateBox a).indicator (fun _ ↦ 1)

theorem boxDensity_nonneg (a : ℝ) (x : Plane) : 0 ≤ boxDensity a x := by
  by_cases h : x ∈ coordinateBox a <;> simp [boxDensity, h]

theorem boxDensity_le_one (a : ℝ) (x : Plane) : boxDensity a x ≤ 1 := by
  by_cases h : x ∈ coordinateBox a <;> simp [boxDensity, h]

theorem integrable_boxDensity (a : ℝ) : Integrable (boxDensity a) := by
  apply (integrable_indicator_iff (isClosed_coordinateBox a).measurableSet).mpr
  exact continuous_const.continuousOn.integrableOn_compact (isCompact_coordinateBox a)

theorem boxDensity_eq_product (a : ℝ) (x : Plane) :
    boxDensity a x = ∏ i, realIntervalWindow (2 * a) (x i) := by
  classical
  have hlo : -(2 * a) / 2 = -a := by ring
  have hhi : 2 * a / 2 = a := by ring
  simp only [boxDensity, coordinateBox, realIntervalWindow, hlo, hhi, Fin.prod_univ_two,
    Set.indicator_apply, Set.mem_ofPred_eq, Fin.forall_fin_two, abs_le, Set.mem_Icc]
  split_ifs <;> simp_all

theorem integral_boxDensity {a : ℝ} (ha : 0 < a) :
    (∫ x : Plane, boxDensity a x) = 4 * a ^ 2 := by
  simp_rw [boxDensity_eq_product]
  rw [integral_plane_product (fun _ t ↦ realIntervalWindow (2 * a) t)]
  simp only [integral_realIntervalWindow (by positivity : 0 < 2 * a), Fin.prod_univ_two]
  ring

theorem volume_real_coordinateBox {a : ℝ} (ha : 0 < a) :
    volume.real (coordinateBox a) = 4 * a ^ 2 := by
  have h := integral_boxDensity ha
  rw [boxDensity, integral_indicator (isClosed_coordinateBox a).measurableSet] at h
  simpa using h

theorem finite_points_coordinateBox {S : Set Plane} (hS : Admissible S) (M : ℝ) :
    (S ∩ coordinateBox M).Finite :=
  (locallyFinitePoints_iff_compact S).mp hS.2 _ (isCompact_coordinateBox M)

noncomputable def cutoffPoints (S : Set Plane) (hS : Admissible S) (M : ℝ) : Finset Plane :=
  (finite_points_coordinateBox hS M).toFinset

@[simp] theorem mem_cutoffPoints (S : Set Plane) (hS : Admissible S) (M : ℝ) (x : Plane) :
    x ∈ cutoffPoints S hS M ↔ x ∈ S ∧ x ∈ coordinateBox M := by
  simp [cutoffPoints]

theorem disk_subset_coordinateBox {M R r : ℝ} {x : Plane}
    (hx : x ∈ coordinateBox (M - R)) (hr : r ≤ R) :
    Metric.closedBall x r ⊆ coordinateBox M := by
  intro y hy i
  have hyx : dist y x ≤ r := hy
  have hcoord : |y i - x i| ≤ dist y x := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le y x i
  have htri := abs_add_le (y i - x i) (x i)
  have hi := hx i
  rw [sub_add_cancel] at htri
  linarith

theorem cutoff_diskPoints_eq {S : Set Plane} (hS : Admissible S) {M R r : ℝ} {x : Plane}
    (hx : x ∈ coordinateBox (M - R)) (hr : r ≤ R) :
    diskPoints (↑(cutoffPoints S hS M) : Set Plane) x r = diskPoints S x r := by
  ext y
  simp only [diskPoints, Set.mem_ofPred_eq, Finset.mem_coe, mem_cutoffPoints]
  constructor
  · rintro ⟨⟨hS', _⟩, hd⟩
    exact ⟨hS', hd⟩
  · rintro ⟨hS', hd⟩
    exact ⟨⟨hS', disk_subset_coordinateBox hx hr hd⟩, hd⟩

theorem no_cutoff_point_near_exterior {S : Set Plane} (hS : Admissible S)
    {M R r : ℝ} {x y : Plane} (hx : x ∉ coordinateBox (M + R)) (hr : r ≤ R)
    (hy : y ∈ cutoffPoints S hS M) : ¬ dist y x ≤ r := by
  intro hd
  have hybox := (mem_cutoffPoints S hS M y).mp hy |>.2
  have hyinner : y ∈ coordinateBox ((M + R) - R) := by simpa using hybox
  apply hx
  exact disk_subset_coordinateBox hyinner hr (by simpa [dist_comm] using hd)

theorem coordinateBox_mono {a b : ℝ} (h : a ≤ b) : coordinateBox a ⊆ coordinateBox b := by
  intro x hx i
  exact (hx i).trans h

theorem coordinate_shell_area {M R : ℝ} (hR : 0 ≤ R) (hM : R < M) :
    volume.real (coordinateBox (M + R) \ coordinateBox (M - R)) = 16 * M * R := by
  rw [measureReal_sdiff (coordinateBox_mono (by linarith : M - R ≤ M + R))
    (isClosed_coordinateBox (M - R)).measurableSet
    (isCompact_coordinateBox (M + R)).measure_lt_top.ne]
  rw [volume_real_coordinateBox (by linarith : 0 < M + R),
    volume_real_coordinateBox (by linarith : 0 < M - R)]
  ring

/-- The frequency lower bound instantiated by an actual spatial square indicator. -/
theorem finite_square_spectral_lower (P : Finset Plane) (M : ℝ) :
    8 * P.card ≤ ∫ ξ in coordinateBox 4,
      ‖atomicFourier P ξ - (𝓕 (fun y : Plane ↦ (boxDensity M y : ℂ)) : Plane → ℂ) ξ‖ ^ 2 :=
  fixed_box_discrepancy_energy_lower P (integrable_boxDensity M)
    (boxDensity_nonneg M) (boxDensity_le_one M)

end DiskDiscrepancy
