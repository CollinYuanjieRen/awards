import MerLeanExperiment.ScaledCells
import MerLeanExperiment.BoundaryCells

open Set MeasureTheory

namespace DiskDiscrepancy

noncomputable section

noncomputable def midpointBoxRadius (q : ℕ) (center : Plane) (radius : ℝ) : ℤ :=
  ⌈(q : ℝ) * (‖center‖ + |radius| + 1)⌉

noncomputable def midpointIndexBox (q : ℕ) (center : Plane) (radius : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-midpointBoxRadius q center radius) (midpointBoxRadius q center radius)).product
    (Finset.Icc (-midpointBoxRadius q center radius) (midpointBoxRadius q center radius))

noncomputable def midpointDiskIndices (q : ℕ) (center : Plane) (radius : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (midpointIndexBox q center radius).filter
    (fun z ↦ gridMidpoint q z ∈ Metric.closedBall center radius)

theorem midpoint_mem_indexBox {q : ℕ} (hq : 0 < q) {center : Plane} {radius : ℝ}
    {z : ℤ × ℤ} (hz : gridMidpoint q z ∈ Metric.closedBall center radius) :
    z ∈ midpointIndexBox q center radius := by
  have hdr : dist (gridMidpoint q z) center ≤ radius := by
    simpa [Metric.mem_closedBall] using hz
  have hnorm : ‖gridMidpoint q z‖ ≤ ‖center‖ + |radius| := by
    calc
      ‖gridMidpoint q z‖ = dist (gridMidpoint q z) 0 := by rw [dist_zero_right]
      _ ≤ dist (gridMidpoint q z) center + dist center 0 := dist_triangle _ _ _
      _ ≤ radius + ‖center‖ := by rw [dist_zero_right]; linarith
      _ ≤ ‖center‖ + |radius| := by linarith [le_abs_self radius]
  have hqR : 0 < (q : ℝ) := by positivity
  have hcoord (i : Fin 2) : |(gridMidpoint q z) i| ≤ ‖center‖ + |radius| :=
    (abs_apply_le_norm _ i).trans hnorm
  have hb1 : |(z.1 : ℝ)| < (q : ℝ) * (‖center‖ + |radius| + 1) := by
    have hc := hcoord 0
    simp [gridMidpoint] at hc
    rw [abs_div, abs_of_pos hqR] at hc
    have hab : |(z.1 : ℝ)| ≤ |(z.1 : ℝ) + 1 / 2| + 1 / 2 := by
      calc
        |(z.1 : ℝ)| = |((z.1 : ℝ) + 1 / 2) - 1 / 2| := by ring_nf
        _ ≤ |(z.1 : ℝ) + 1 / 2| + |(1 / 2 : ℝ)| := abs_sub _ _
        _ = _ := by norm_num
    have := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (q : ℝ))
    field_simp at this
    have heq : |((z.1 : ℝ) * 2 + 1) / 2| = |(z.1 : ℝ) + 1 / 2| := by
      apply congrArg abs
      ring
    rw [heq] at this
    have hql : (1 / 2 : ℝ) < q := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    nlinarith
  have hb2 : |(z.2 : ℝ)| < (q : ℝ) * (‖center‖ + |radius| + 1) := by
    have hc := hcoord 1
    simp [gridMidpoint] at hc
    rw [abs_div, abs_of_pos hqR] at hc
    have hab : |(z.2 : ℝ)| ≤ |(z.2 : ℝ) + 1 / 2| + 1 / 2 := by
      calc
        |(z.2 : ℝ)| = |((z.2 : ℝ) + 1 / 2) - 1 / 2| := by ring_nf
        _ ≤ |(z.2 : ℝ) + 1 / 2| + |(1 / 2 : ℝ)| := abs_sub _ _
        _ = _ := by norm_num
    have := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (q : ℝ))
    field_simp at this
    have heq : |((z.2 : ℝ) * 2 + 1) / 2| = |(z.2 : ℝ) + 1 / 2| := by
      apply congrArg abs
      ring
    rw [heq] at this
    have hql : (1 / 2 : ℝ) < q := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    nlinarith
  have bounds (a : ℤ) (h : |(a : ℝ)| < (q : ℝ) * (‖center‖ + |radius| + 1)) :
      -midpointBoxRadius q center radius ≤ a ∧ a ≤ midpointBoxRadius q center radius := by
    have hu : a ≤ midpointBoxRadius q center radius :=
      le_of_lt (Int.lt_ceil.mpr (lt_of_le_of_lt (le_abs_self _) h))
    have hn : ((-a : ℤ) : ℝ) < (q : ℝ) * (‖center‖ + |radius| + 1) := by
      norm_num
      exact lt_of_le_of_lt (neg_le_abs _) h
    have hl' : -a ≤ midpointBoxRadius q center radius :=
      le_of_lt (Int.lt_ceil.mpr hn)
    exact ⟨by omega, hu⟩
  have b1 := bounds z.1 hb1
  have b2 := bounds z.2 hb2
  simp [midpointIndexBox, b1.1, b1.2, b2.1, b2.2]

@[simp] theorem mem_midpointDiskIndices {q : ℕ} (hq : 0 < q) {center : Plane}
    {radius : ℝ} {z : ℤ × ℤ} :
    z ∈ midpointDiskIndices q center radius ↔
      gridMidpoint q z ∈ Metric.closedBall center radius := by
  classical
  rw [midpointDiskIndices, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨midpoint_mem_indexBox hq h, h⟩

def midpointCellUnion (q : ℕ) (center : Plane) (radius : ℝ) : Set Plane :=
  ⋃ z ∈ midpointDiskIndices q center radius, scaledCell q z

 theorem volume_midpointCellUnion {q : ℕ} (hq : 0 < q) (center : Plane) (radius : ℝ) :
    volume (midpointCellUnion q center radius) =
      (midpointDiskIndices q center radius).card * ENNReal.ofReal (1 / (q : ℝ) ^ 2) := by
  unfold midpointCellUnion
  rw [measure_biUnion_finset]
  · simp [volume_scaledCell hq]
  · intro z _ w _ hzw
    exact scaledCell_disjoint hq hzw
  · intro z _
    exact measurableSet_scaledCell q z

 theorem midpointCellUnion_subset_outer {q : ℕ} (hq : 0 < q) {center : Plane}
    {radius : ℝ} : midpointCellUnion q center radius ⊆
      Metric.closedBall center (radius + 2 / q) := by
  intro x hx
  simp only [midpointCellUnion, mem_iUnion] at hx
  obtain ⟨z, hzmem, hxcell⟩ := hx
  have hm := (mem_midpointDiskIndices hq).mp hzmem
  rw [Metric.mem_closedBall] at hm ⊢
  apply le_of_lt
  calc
    dist x center ≤ dist x (gridMidpoint q z) + dist (gridMidpoint q z) center := dist_triangle _ _ _
    _ < 2 / q + radius := add_lt_add_of_lt_of_le (dist_gridMidpoint_lt hq hxcell) hm
    _ ≤ radius + 2 / q := by linarith

 theorem inner_subset_midpointCellUnion {q : ℕ} (hq : 0 < q) {center : Plane}
    {radius : ℝ} : Metric.closedBall center (radius - 2 / q) ⊆
      midpointCellUnion q center radius := by
  intro x hx
  obtain ⟨z, hxcell⟩ := exists_mem_scaledCell q hq x
  have hxm : dist x (gridMidpoint q z) < 2 / q := dist_gridMidpoint_lt hq hxcell
  have hxr : dist x center ≤ radius - 2 / q := by
    simpa [Metric.mem_closedBall] using hx
  have hm : gridMidpoint q z ∈ Metric.closedBall center radius := by
    rw [Metric.mem_closedBall]
    apply le_of_lt
    calc
      dist (gridMidpoint q z) center ≤ dist (gridMidpoint q z) x + dist x center := dist_triangle _ _ _
      _ < 2 / q + (radius - 2 / q) := add_lt_add_of_lt_of_le (by simpa [dist_comm] using hxm) hxr
      _ ≤ radius := by linarith
  simp only [midpointCellUnion, mem_iUnion]
  exact ⟨z, (mem_midpointDiskIndices hq).mpr hm, hxcell⟩

def midpointGridArea (q : ℕ) (center : Plane) (radius : ℝ) : ℝ :=
  (midpointDiskIndices q center radius).card / (q : ℝ) ^ 2

theorem midpointGridArea_eq_volumeReal {q : ℕ} (hq : 0 < q)
    (center : Plane) (radius : ℝ) :
    midpointGridArea q center radius = volume.real (midpointCellUnion q center radius) := by
  rw [measureReal_def, volume_midpointCellUnion hq]
  unfold midpointGridArea
  rw [ENNReal.toReal_mul]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (q : ℝ) ^ 2)]
  field_simp

/-- Uniform midpoint-grid quadrature error for disks. -/
theorem midpointGridArea_error_le {q : ℕ} {center : Plane} {radius R : ℝ}
    (hR : 4 ≤ R) (hqR : R ≤ q) (hr : 0 ≤ radius) (hrR : radius ≤ R + 1) :
    |midpointGridArea q center radius - Real.pi * radius ^ 2| ≤ 256 := by
  have hq : 0 < q := by
    have : (0 : ℝ) < q := lt_of_lt_of_le (by linarith) hqR
    exact_mod_cast this
  have hqRpos : 0 < (q : ℝ) := by positivity
  let d : ℝ := 2 / q
  have hd : 0 < d := by dsimp [d]; positivity
  have houter0 : 0 ≤ radius + d := by positivity
  rw [midpointGridArea_eq_volumeReal hq]
  apply abs_le.mpr
  constructor
  · by_cases hrd : radius ≤ d
    · have hnonneg : 0 ≤ volume.real (midpointCellUnion q center radius) := measureReal_nonneg
      have hpi := Real.pi_le_four
      have hdle : d ≤ 1 / 2 := by
        dsimp [d]
        have hq4 : (4 : ℝ) ≤ q := hR.trans hqR
        apply (div_le_iff₀ hqRpos).2
        nlinarith
      nlinarith [sq_nonneg radius]
    · have hinner0 : 0 ≤ radius - d := by linarith
      have hlower : volume.real (Metric.closedBall center (radius - d)) ≤
          volume.real (midpointCellUnion q center radius) := by
        exact measureReal_mono (inner_subset_midpointCellUnion hq)
          (h₂ := measure_ne_top_of_subset (midpointCellUnion_subset_outer hq)
            (isCompact_closedBall center (radius + d)).measure_ne_top)
      rw [volumeReal_closedBall center hinner0] at hlower
      have hpi := Real.pi_le_four
      have hdle : d ≤ 1 / 2 := by
        dsimp [d]
        have hq4 : (4 : ℝ) ≤ q := hR.trans hqR
        apply (div_le_iff₀ hqRpos).2
        nlinarith
      have hr8 : radius ≤ R + 1 := hrR
      have hdR : d * radius ≤ 3 := by
        dsimp [d]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hqRpos).2
        nlinarith [mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ (q : ℝ) - R by linarith)]
      nlinarith [Real.pi_pos.le, sq_nonneg d]
  · have hupper : volume.real (midpointCellUnion q center radius) ≤
        volume.real (Metric.closedBall center (radius + d)) := by
      exact measureReal_mono (midpointCellUnion_subset_outer hq)
        (h₂ := (isCompact_closedBall center (radius + d)).measure_ne_top)
    rw [volumeReal_closedBall center houter0] at hupper
    have hpi := Real.pi_le_four
    have hdle : d ≤ 1 / 2 := by
      dsimp [d]
      have hq4 : (4 : ℝ) ≤ q := hR.trans hqR
      apply (div_le_iff₀ hqRpos).2
      nlinarith
    have hdR : d * radius ≤ 3 := by
      dsimp [d]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hqRpos).2
      nlinarith [mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ (q : ℝ) - R by linarith)]
    nlinarith [Real.pi_pos.le, sq_nonneg d]

end
end DiskDiscrepancy
