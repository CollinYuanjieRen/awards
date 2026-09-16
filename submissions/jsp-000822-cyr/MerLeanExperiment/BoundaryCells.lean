import MerLeanExperiment.GridCells
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Measure.Real

open Set MeasureTheory

namespace DiskDiscrepancy

noncomputable def boundaryBoxRadius (center : Plane) (radius : ℝ) : ℤ :=
  ⌈‖center‖ + radius + 2⌉

noncomputable def boundaryCellBox (center : Plane) (radius : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(boundaryBoxRadius center radius)) (boundaryBoxRadius center radius)).product
    (Finset.Icc (-(boundaryBoxRadius center radius)) (boundaryBoxRadius center radius))

noncomputable def boundaryCells (center : Plane) (radius : ℝ) : Finset (ℤ × ℤ) :=
  by
    classical
    exact (boundaryCellBox center radius).filter (BoundaryCell center radius)

/-- A cell which meets a nonnegative-radius disk lies in the explicit finite
integer box used by `boundaryCells`. -/
theorem meetingCell_mem_boundaryCellBox {center : Plane} {radius : ℝ} (_hr : 0 ≤ radius)
    {z : ℤ × ℤ} (hz : (unitCell z ∩ Metric.closedBall center radius).Nonempty) :
    z ∈ boundaryCellBox center radius := by
  obtain ⟨x, hxcell, hxdisk⟩ := hz
  have hxc : dist x center ≤ radius := by
    simpa [Metric.mem_closedBall] using hxdisk
  have hcorner : dist (latticeCorner z) center < radius + 2 := by
    calc
      dist (latticeCorner z) center ≤
          dist (latticeCorner z) x + dist x center := dist_triangle _ _ _
      _ < 2 + radius := add_lt_add_of_lt_of_le
        (by simpa [dist_comm] using dist_latticeCorner_lt_two hxcell) hxc
      _ = radius + 2 := by ring
  have hnorm : ‖latticeCorner z‖ < ‖center‖ + radius + 2 := by
    calc
      ‖latticeCorner z‖ = dist (latticeCorner z) 0 := by rw [dist_zero_right]
      _ ≤ dist (latticeCorner z) center + dist center 0 := dist_triangle _ _ _
      _ < (radius + 2) + ‖center‖ := by
        rw [dist_zero_right]
        linarith
      _ = ‖center‖ + radius + 2 := by ring
  have hcoord (i : Fin 2) : |(latticeCorner z) i| < ‖center‖ + radius + 2 :=
    lt_of_le_of_lt (abs_apply_le_norm (latticeCorner z) i) hnorm
  have hz1 : (z.1 : ℝ) < ‖center‖ + radius + 2 := by
    have := hcoord 0
    simp [latticeCorner] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hnz1 : (-(z.1 : ℤ) : ℝ) < ‖center‖ + radius + 2 := by
    have := hcoord 0
    simp [latticeCorner] at this
    exact lt_of_le_of_lt (neg_le_abs _) this
  have hz2 : (z.2 : ℝ) < ‖center‖ + radius + 2 := by
    have := hcoord 1
    simp [latticeCorner] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hnz2 : (-(z.2 : ℤ) : ℝ) < ‖center‖ + radius + 2 := by
    have := hcoord 1
    simp [latticeCorner] at this
    exact lt_of_le_of_lt (neg_le_abs _) this
  have hu1 : z.1 ≤ boundaryBoxRadius center radius := by
    exact le_trans (le_of_lt (Int.lt_ceil.mpr hz1)) (le_refl _)
  have hl1 : -boundaryBoxRadius center radius ≤ z.1 := by
    have hnz1' : ((-z.1 : ℤ) : ℝ) < ‖center‖ + radius + 2 := by
      norm_num
      exact hnz1
    have : -z.1 ≤ boundaryBoxRadius center radius :=
      le_of_lt (Int.lt_ceil.mpr hnz1')
    omega
  have hu2 : z.2 ≤ boundaryBoxRadius center radius := by
    exact le_of_lt (Int.lt_ceil.mpr hz2)
  have hl2 : -boundaryBoxRadius center radius ≤ z.2 := by
    have hnz2' : ((-z.2 : ℤ) : ℝ) < ‖center‖ + radius + 2 := by
      norm_num
      exact hnz2
    have : -z.2 ≤ boundaryBoxRadius center radius :=
      le_of_lt (Int.lt_ceil.mpr hnz2')
    omega
  simp [boundaryCellBox, hl1, hu1, hl2, hu2]

theorem boundaryCell_mem_box {center : Plane} {radius : ℝ} (hr : 0 ≤ radius)
    {z : ℤ × ℤ} (hz : BoundaryCell center radius z) :
    z ∈ boundaryCellBox center radius :=
  meetingCell_mem_boundaryCellBox hr hz.1

@[simp] theorem mem_boundaryCells {center : Plane} {radius : ℝ} (hr : 0 ≤ radius)
    {z : ℤ × ℤ} :
    z ∈ boundaryCells center radius ↔ BoundaryCell center radius z := by
  classical
  rw [boundaryCells, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨boundaryCell_mem_box hr h, h⟩

/-- The set of actual boundary-cell indices is finite. -/
theorem finite_boundaryCell_set {center : Plane} {radius : ℝ} (hr : 0 ≤ radius) :
    {z : ℤ × ℤ | BoundaryCell center radius z}.Finite := by
  refine (boundaryCells center radius).finite_toSet.subset ?_
  intro z hz
  simpa [mem_boundaryCells hr] using hz

def boundaryCellUnion (center : Plane) (radius : ℝ) : Set Plane :=
  ⋃ z ∈ boundaryCells center radius, unitCell z

theorem volume_boundaryCellUnion {center : Plane} {radius : ℝ} :
    volume (boundaryCellUnion center radius) = (boundaryCells center radius).card := by
  unfold boundaryCellUnion
  rw [measure_biUnion_finset]
  · simp [volume_unitCell]
  · intro z _ w _ hzw
    exact unitCell_disjoint hzw
  · intro z _
    exact measurableSet_unitCell z

/-- Every point of a boundary cell lies in the width-four shell around the
circle. -/
theorem boundaryCellUnion_subset_shell {center : Plane} {radius : ℝ} (hr : 0 ≤ radius) :
    boundaryCellUnion center radius ⊆
      Metric.closedBall center (radius + 4) \ Metric.ball center (radius - 4) := by
  intro p hp
  simp only [boundaryCellUnion, mem_iUnion] at hp
  obtain ⟨z, hz⟩ := hp
  obtain ⟨hzmem, hpcell⟩ := hz
  have hzboundary : BoundaryCell center radius z := (mem_boundaryCells hr).mp hzmem
  obtain ⟨x, hxcell, hxin⟩ := hzboundary.1
  obtain ⟨y, hycell, hyout⟩ := hzboundary.2
  have hxin' : dist x center ≤ radius := by
    simpa [Metric.mem_closedBall] using hxin
  have hyout' : radius < dist y center := by
    simpa [Metric.mem_closedBall, not_le] using hyout
  constructor
  · rw [Metric.mem_closedBall]
    apply le_of_lt
    calc
      dist p center ≤ dist p x + dist x center := dist_triangle _ _ _
      _ < 4 + radius := add_lt_add_of_lt_of_le
        (dist_lt_four_of_mem_unitCell hpcell hxcell) hxin'
      _ ≤ radius + 4 := by linarith
  · rw [Metric.mem_ball, not_lt]
    have hpy : dist p y < 4 := dist_lt_four_of_mem_unitCell hpcell hycell
    calc
      radius - 4 ≤ dist y center - dist p y := by linarith
      _ ≤ dist p center := by
        have htri := dist_triangle y p center
        rw [dist_comm y p] at htri
        linarith

theorem volumeReal_closedBall (center : Plane) {s : ℝ} (hs : 0 ≤ s) :
    volume.real (Metric.closedBall center s) = Real.pi * s ^ 2 := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs,
    ENNReal.toReal_ofReal Real.pi_nonneg]
  ring

theorem volumeReal_ball (center : Plane) {s : ℝ} (hs : 0 ≤ s) :
    volume.real (Metric.ball center s) = Real.pi * s ^ 2 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs,
    ENNReal.toReal_ofReal Real.pi_nonneg]
  ring

/-- Generous linear bound for the actual finite boundary-cell set. -/
theorem boundaryCells_card_le {center : Plane} {radius R : ℝ}
    (hR : 4 ≤ R) (hr : 0 ≤ radius) (hrR : radius ≤ R + 1) :
    ((boundaryCells center radius).card : ℝ) ≤ 120 * R := by
  have hcard : ((boundaryCells center radius).card : ℝ) =
      volume.real (boundaryCellUnion center radius) := by
    rw [measureReal_def, volume_boundaryCellUnion]
    simp
  rw [hcard]
  have houter0 : 0 ≤ radius + 4 := by linarith
  have hmono : volume.real (boundaryCellUnion center radius) ≤
      volume.real (Metric.closedBall center (radius + 4)) := by
    apply measureReal_mono
    exact (boundaryCellUnion_subset_shell hr).trans sdiff_subset
    exact (isCompact_closedBall center (radius + 4)).measure_ne_top
  by_cases hsmall : radius ≤ 4
  · rw [volumeReal_closedBall center houter0] at hmono
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    calc
      volume.real (boundaryCellUnion center radius) ≤ Real.pi * (radius + 4) ^ 2 := hmono
      _ ≤ 4 * 8 ^ 2 := by nlinarith [Real.pi_pos]
      _ ≤ 120 * R := by nlinarith
  · have hinner0 : 0 ≤ radius - 4 := by linarith
    have hballsub : Metric.ball center (radius - 4) ⊆
        Metric.closedBall center (radius + 4) := by
      intro x hx
      rw [Metric.mem_ball] at hx
      rw [Metric.mem_closedBall]
      linarith
    have hshell : volume.real
        (Metric.closedBall center (radius + 4) \ Metric.ball center (radius - 4)) =
        16 * Real.pi * radius := by
      rw [measureReal_sdiff hballsub measurableSet_ball
          (isCompact_closedBall center (radius + 4)).measure_ne_top,
        volumeReal_closedBall center houter0, volumeReal_ball center hinner0]
      ring
    have hshellmono : volume.real (boundaryCellUnion center radius) ≤
        volume.real
          (Metric.closedBall center (radius + 4) \ Metric.ball center (radius - 4)) := by
      exact measureReal_mono (boundaryCellUnion_subset_shell hr)
        (h₂ := measure_ne_top_of_subset sdiff_subset
          (isCompact_closedBall center (radius + 4)).measure_ne_top)
    rw [hshell] at hshellmono
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    calc
      volume.real (boundaryCellUnion center radius) ≤ 16 * Real.pi * radius := hshellmono
      _ ≤ 64 * radius := by nlinarith [Real.pi_pos]
      _ ≤ 120 * R := by nlinarith

end DiskDiscrepancy
