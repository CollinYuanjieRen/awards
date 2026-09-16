import MerLeanExperiment.DiskModel
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set MeasureTheory

namespace DiskDiscrepancy

/-- The integer lower-left corner of a lattice cell. -/
def latticeCorner (z : ℤ × ℤ) : Plane :=
  WithLp.toLp 2 ![(z.1 : ℝ), (z.2 : ℝ)]

/-- The half-open unit lattice cell based at `z`. -/
def unitCell (z : ℤ × ℤ) : Set Plane :=
  {x | (z.1 : ℝ) ≤ x 0 ∧ x 0 < z.1 + 1 ∧
    (z.2 : ℝ) ≤ x 1 ∧ x 1 < z.2 + 1}

@[simp] theorem mem_unitCell {z : ℤ × ℤ} {x : Plane} :
    x ∈ unitCell z ↔
      (z.1 : ℝ) ≤ x 0 ∧ x 0 < z.1 + 1 ∧
      (z.2 : ℝ) ≤ x 1 ∧ x 1 < z.2 + 1 := by
  rfl

theorem abs_apply_le_norm (x : Plane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have hs := EuclideanSpace.real_norm_sq_eq x
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, hs]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)

/-- Every point of a half-open unit cell is within distance two of its integer
corner.  The loose constant avoids square-root bookkeeping downstream. -/
theorem dist_latticeCorner_lt_two {z : ℤ × ℤ} {x : Plane}
    (hx : x ∈ unitCell z) : dist x (latticeCorner z) < 2 := by
  rw [dist_eq_norm]
  have h0a : 0 ≤ x 0 - (z.1 : ℝ) := sub_nonneg.mpr (mem_unitCell.mp hx).1
  have h0b : x 0 - (z.1 : ℝ) < 1 := by linarith [(mem_unitCell.mp hx).2.1]
  have h1a : 0 ≤ x 1 - (z.2 : ℝ) := sub_nonneg.mpr (mem_unitCell.mp hx).2.2.1
  have h1b : x 1 - (z.2 : ℝ) < 1 := by linarith [(mem_unitCell.mp hx).2.2.2]
  have hs : ‖x - latticeCorner z‖ ^ 2 < 4 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, PiLp.sub_apply, latticeCorner,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [sq_nonneg (x 0 - (z.1 : ℝ)), sq_nonneg (x 1 - (z.2 : ℝ))]
  nlinarith [norm_nonneg (x - latticeCorner z)]

theorem dist_lt_four_of_mem_unitCell {z : ℤ × ℤ} {x y : Plane}
    (hx : x ∈ unitCell z) (hy : y ∈ unitCell z) : dist x y < 4 := by
  calc
    dist x y ≤ dist x (latticeCorner z) + dist (latticeCorner z) y := dist_triangle _ _ _
    _ < 2 + 2 := add_lt_add (dist_latticeCorner_lt_two hx)
      (by simpa [dist_comm] using dist_latticeCorner_lt_two hy)
    _ = 4 := by norm_num

theorem measurableSet_unitCell (z : ℤ × ℤ) : MeasurableSet (unitCell z) := by
  unfold unitCell
  measurability

/-- Distinct half-open lattice cells are disjoint. -/
theorem unitCell_disjoint {z w : ℤ × ℤ} (hzw : z ≠ w) :
    Disjoint (unitCell z) (unitCell w) := by
  rw [Set.disjoint_left]
  intro x hxz hxw
  have hz := mem_unitCell.mp hxz
  have hw := mem_unitCell.mp hxw
  apply hzw
  apply Prod.ext
  · have h₁r : (z.1 : ℝ) < ((w.1 + 1 : ℤ) : ℝ) := by
      norm_num
      exact lt_of_le_of_lt hz.1 hw.2.1
    have h₂r : (w.1 : ℝ) < ((z.1 + 1 : ℤ) : ℝ) := by
      norm_num
      exact lt_of_le_of_lt hw.1 hz.2.1
    have h₁ : z.1 < w.1 + 1 := Int.cast_lt.mp h₁r
    have h₂ : w.1 < z.1 + 1 := Int.cast_lt.mp h₂r
    omega
  · have h₁r : (z.2 : ℝ) < ((w.2 + 1 : ℤ) : ℝ) := by
      norm_num
      exact lt_of_le_of_lt hz.2.2.1 hw.2.2.2
    have h₂r : (w.2 : ℝ) < ((z.2 + 1 : ℤ) : ℝ) := by
      norm_num
      exact lt_of_le_of_lt hw.2.2.1 hz.2.2.2
    have h₁ : z.2 < w.2 + 1 := Int.cast_lt.mp h₁r
    have h₂ : w.2 < z.2 + 1 := Int.cast_lt.mp h₂r
    omega

/-- Every half-open unit lattice cell has area one. -/
theorem volume_unitCell (z : ℤ × ℤ) : volume (unitCell z) = 1 := by
  let s : Set (Fin 2 → ℝ) := pi univ fun i =>
    Ico (![z.1, z.2] i : ℝ) (![z.1 + 1, z.2 + 1] i : ℝ)
  have hs : MeasurableSet s := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico
  have heq : (WithLp.ofLp ⁻¹' s : Set Plane) = unitCell z := by
    ext x
    simp [s, unitCell, Fin.forall_fin_two]
    tauto
  calc
    volume (unitCell z) = volume (WithLp.ofLp ⁻¹' s) := by rw [heq]
    _ = volume s := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      hs.nullMeasurableSet
    _ = 1 := by
      dsimp [s]
      rw [Real.volume_pi_Ico]
      simp [Fin.prod_univ_two]

/-- A boundary cell meets both the disk and its complement. -/
def BoundaryCell (center : Plane) (radius : ℝ) (z : ℤ × ℤ) : Prop :=
  (unitCell z ∩ Metric.closedBall center radius).Nonempty ∧
  (unitCell z \ Metric.closedBall center radius).Nonempty

end DiskDiscrepancy
