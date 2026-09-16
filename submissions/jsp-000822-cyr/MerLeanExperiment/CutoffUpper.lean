import MerLeanExperiment.CutoffSpatial

open MeasureTheory

namespace DiskDiscrepancy

theorem cutoff_count_le {S : Set Plane} (hS : Admissible S) (M r : ℝ) (x : Plane) :
    pointCount (↑(cutoffPoints S hS M) : Set Plane) x r ≤ pointCount S x r := by
  apply Set.ncard_le_ncard _ (hS.2 x r)
  intro y hy
  exact ⟨((mem_cutoffPoints S hS M y).mp hy.1).1, hy.2⟩

theorem norm_cutoffSignal_le_of_discrepancy {S : Set Plane} (hS : Admissible S)
    {M r D : ℝ} {x : Plane} (hr : 0 ≤ r) (hD : discrepancy S x r ≤ D) :
    ‖cutoffSignal (cutoffPoints S hS M) M r x‖ ≤ 2 * Real.pi * r ^ 2 + D := by
  have hc : (pointCount (↑(cutoffPoints S hS M) : Set Plane) x r : ℝ) ≤ pointCount S x r :=
    Nat.cast_le.mpr (cutoff_count_le hS M r x)
  have hD0 : 0 ≤ D := (discrepancy_nonneg S x r).trans hD
  change |(pointCount S x r : ℝ) - Real.pi * r ^ 2| ≤ D at hD
  have hSup := (abs_le.mp hD).2
  have hb0 := areaBackground_nonneg M r x
  have hb := areaBackground_le_area M hr x
  have hc0 : (0 : ℝ) ≤ pointCount (↑(cutoffPoints S hS M) : Set Plane) x r := Nat.cast_nonneg _
  rw [norm_cutoffSignal]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg r)]

/-- Integrate separate interior and boundary-strip bounds with their exact areas. -/
theorem integral_le_coordinate_shell {f : Plane → ℝ} (hf : Integrable f)
    {M R A B : ℝ} (hR : 0 ≤ R) (hM : R < M)
    (hinner : ∀ x ∈ coordinateBox (M - R), f x ≤ A)
    (hshell : ∀ x ∈ coordinateBox (M + R) \ coordinateBox (M - R), f x ≤ B)
    (houter : ∀ x ∉ coordinateBox (M + R), f x = 0) :
    (∫ x : Plane, f x) ≤ 4 * (M - R) ^ 2 * A + 16 * M * R * B := by
  let I := coordinateBox (M - R)
  let E := coordinateBox (M + R) \ coordinateBox (M - R)
  have hi : MeasurableSet I := (isClosed_coordinateBox _).measurableSet
  have he : MeasurableSet E := (isClosed_coordinateBox _).measurableSet.diff hi
  have hiFin : volume I ≠ ⊤ := (isCompact_coordinateBox _).measure_ne_top
  have heFin : volume E ≠ ⊤ :=
    measure_ne_top_of_subset Set.sdiff_subset (isCompact_coordinateBox (M + R)).measure_ne_top
  have hiInt : Integrable (I.indicator (fun _ : Plane ↦ A)) :=
    (integrable_indicator_iff hi).mpr (integrableOn_const hiFin)
  have heInt : Integrable (E.indicator (fun _ : Plane ↦ B)) :=
    (integrable_indicator_iff he).mpr (integrableOn_const heFin)
  have hbound (x : Plane) : f x ≤ I.indicator (fun _ ↦ A) x + E.indicator (fun _ ↦ B) x := by
    by_cases hxI : x ∈ I
    · have hxE : x ∉ E := fun h ↦ h.2 hxI
      simpa [hxI, hxE] using hinner x hxI
    · by_cases hxO : x ∈ coordinateBox (M + R)
      · have hxE : x ∈ E := ⟨hxO, hxI⟩
        simpa [hxI, hxE] using hshell x hxE
      · have hxE : x ∉ E := fun h ↦ hxO h.1
        simp [hxI, hxE, houter x hxO]
  have h := integral_mono hf (hiInt.add heInt) hbound
  simp only [Pi.add_apply] at h
  rw [integral_add hiInt heInt, integral_indicator hi, integral_indicator he] at h
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at h
  dsimp [I, E] at h
  rwa [volume_real_coordinateBox (by linarith : 0 < M - R), coordinate_shell_area hR hM] at h

/-- A spatial energy estimate for each strictly positive tested radius. -/
theorem cutoffSignal_energy_upper {S : Set Plane} (hS : Admissible S)
    {M R r D : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hM : R < M)
    (hD : D ≤ R ^ 2) (hbound : ∀ x : Plane, discrepancy S x r ≤ D) :
    (∫ x : Plane, ‖cutoffSignal (cutoffPoints S hS M) M r x‖ ^ 2) ≤
      4 * M ^ 2 * D ^ 2 + 16 * (2 * Real.pi + 1) ^ 2 * M * R ^ 5 := by
  have hR : 0 < R := hr.trans_le hrR
  have hD0 : 0 ≤ D := (discrepancy_nonneg S 0 r).trans (hbound 0)
  have hsignalInt : Integrable (fun x : Plane ↦ ‖cutoffSignal (cutoffPoints S hS M) M r x‖ ^ 2) :=
    (memLp_cutoffSignal (cutoffPoints S hS M) M hr.le).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hraw := integral_le_coordinate_shell hsignalInt hR.le hM
    (A := D ^ 2) (B := ((2 * Real.pi + 1) * R ^ 2) ^ 2)
    (fun x hx ↦ by
      rw [cutoffSignal_interior hS hx hrR hr.le]
      exact pow_le_pow_left₀ (discrepancy_nonneg S x r) (hbound x) 2)
    (fun x _ ↦ by
      have hnorm := norm_cutoffSignal_le_of_discrepancy (M := M) hS hr.le (hbound x)
      have hsq : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr.le hrR 2
      have hnorm' : ‖cutoffSignal (cutoffPoints S hS M) M r x‖ ≤ (2 * Real.pi + 1) * R ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * Real.pi)]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm' 2)
    (fun x hx ↦ by rw [cutoffSignal_exterior hS hx hrR, norm_zero, zero_pow (by decide)])
  have hm2 : (M - R) ^ 2 ≤ M ^ 2 := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 (by norm_num : (0 : ℝ) ≤ 4)) (sq_nonneg D)
  have heq : 16 * M * R * ((2 * Real.pi + 1) * R ^ 2) ^ 2 =
      16 * (2 * Real.pi + 1) ^ 2 * M * R ^ 5 := by ring
  rw [heq] at hraw
  linarith

end DiskDiscrepancy
