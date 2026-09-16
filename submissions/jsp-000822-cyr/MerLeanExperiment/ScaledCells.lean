import MerLeanExperiment.GridCells
import Mathlib.Algebra.Order.Floor.Ring

open Set MeasureTheory

namespace DiskDiscrepancy

noncomputable section

/-- Midpoint of the `q⁻¹` grid cell indexed by an integer pair. -/
def gridMidpoint (q : ℕ) (z : ℤ × ℤ) : Plane :=
  WithLp.toLp 2 ![((z.1 : ℝ) + 1 / 2) / q, ((z.2 : ℝ) + 1 / 2) / q]

/-- Half-open square of side `q⁻¹`. -/
def scaledCell (q : ℕ) (z : ℤ × ℤ) : Set Plane :=
  {x | (z.1 : ℝ) / q ≤ x 0 ∧ x 0 < ((z.1 : ℝ) + 1) / q ∧
    (z.2 : ℝ) / q ≤ x 1 ∧ x 1 < ((z.2 : ℝ) + 1) / q}

@[simp] theorem mem_scaledCell {q : ℕ} {z : ℤ × ℤ} {x : Plane} :
    x ∈ scaledCell q z ↔
      (z.1 : ℝ) / q ≤ x 0 ∧ x 0 < ((z.1 : ℝ) + 1) / q ∧
      (z.2 : ℝ) / q ≤ x 1 ∧ x 1 < ((z.2 : ℝ) + 1) / q := Iff.rfl

theorem gridMidpoint_mem_scaledCell {q : ℕ} (hq : 0 < q) (z : ℤ × ℤ) :
    gridMidpoint q z ∈ scaledCell q z := by
  rw [mem_scaledCell]
  simp only [gridMidpoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hqR : 0 < (q : ℝ) := by positivity
  constructor
  · apply (div_le_div_iff_of_pos_right hqR).2; norm_num
  constructor
  · apply (div_lt_div_iff_of_pos_right hqR).2; norm_num
  constructor
  · apply (div_le_div_iff_of_pos_right hqR).2; norm_num
  · apply (div_lt_div_iff_of_pos_right hqR).2; norm_num

/-- Every point lies in the cell indexed by the coordinatewise floors of `q x`. -/
theorem exists_mem_scaledCell (q : ℕ) (hq : 0 < q) (x : Plane) :
    ∃ z : ℤ × ℤ, x ∈ scaledCell q z := by
  let z : ℤ × ℤ := (⌊(q : ℝ) * x 0⌋, ⌊(q : ℝ) * x 1⌋)
  refine ⟨z, ?_⟩
  rw [mem_scaledCell]
  have hqR : 0 < (q : ℝ) := by positivity
  dsimp [z]
  constructor
  · apply (div_le_iff₀ hqR).2
    simpa [mul_comm] using Int.floor_le ((q : ℝ) * x 0)
  constructor
  · apply (lt_div_iff₀ hqR).2
    simpa [add_comm, mul_comm] using Int.lt_floor_add_one ((q : ℝ) * x 0)
  constructor
  · apply (div_le_iff₀ hqR).2
    simpa [mul_comm] using Int.floor_le ((q : ℝ) * x 1)
  · apply (lt_div_iff₀ hqR).2
    simpa [add_comm, mul_comm] using Int.lt_floor_add_one ((q : ℝ) * x 1)

 theorem scaledCell_disjoint {q : ℕ} (hq : 0 < q) {z w : ℤ × ℤ} (hzw : z ≠ w) :
    Disjoint (scaledCell q z) (scaledCell q w) := by
  rw [Set.disjoint_left]
  intro x hxz hxw
  have hz := mem_scaledCell.mp hxz
  have hw := mem_scaledCell.mp hxw
  have hqR : 0 < (q : ℝ) := by positivity
  apply hzw
  apply Prod.ext
  · have h₁r : (z.1 : ℝ) < (w.1 : ℝ) + 1 := by
      have := lt_of_le_of_lt hz.1 hw.2.1
      apply (div_lt_div_iff_of_pos_right hqR).mp
      simpa [add_div] using this
    have h₂r : (w.1 : ℝ) < (z.1 : ℝ) + 1 := by
      have := lt_of_le_of_lt hw.1 hz.2.1
      apply (div_lt_div_iff_of_pos_right hqR).mp
      simpa [add_div] using this
    have h₁ : z.1 < w.1 + 1 := by exact_mod_cast h₁r
    have h₂ : w.1 < z.1 + 1 := by exact_mod_cast h₂r
    omega
  · have h₁r : (z.2 : ℝ) < (w.2 : ℝ) + 1 := by
      have := lt_of_le_of_lt hz.2.2.1 hw.2.2.2
      apply (div_lt_div_iff_of_pos_right hqR).mp
      simpa [add_div] using this
    have h₂r : (w.2 : ℝ) < (z.2 : ℝ) + 1 := by
      have := lt_of_le_of_lt hw.2.2.1 hz.2.2.2
      apply (div_lt_div_iff_of_pos_right hqR).mp
      simpa [add_div] using this
    have h₁ : z.2 < w.2 + 1 := by exact_mod_cast h₁r
    have h₂ : w.2 < z.2 + 1 := by exact_mod_cast h₂r
    omega

 theorem measurableSet_scaledCell (q : ℕ) (z : ℤ × ℤ) : MeasurableSet (scaledCell q z) := by
  unfold scaledCell
  measurability

 theorem volume_scaledCell {q : ℕ} (hq : 0 < q) (z : ℤ × ℤ) :
    volume (scaledCell q z) = ENNReal.ofReal (1 / (q : ℝ) ^ 2) := by
  let s : Set (Fin 2 → ℝ) := pi univ fun i =>
    Ico (![(z.1 : ℝ) / q, (z.2 : ℝ) / q] i)
      (![ ((z.1 : ℝ) + 1) / q, ((z.2 : ℝ) + 1) / q] i)
  have hs : MeasurableSet s := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico
  have heq : (WithLp.ofLp ⁻¹' s : Set Plane) = scaledCell q z := by
    ext x
    simp [s, scaledCell, Fin.forall_fin_two]
    tauto
  calc
    volume (scaledCell q z) = volume (WithLp.ofLp ⁻¹' s) := by rw [heq]
    _ = volume s := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage hs.nullMeasurableSet
    _ = ENNReal.ofReal (1 / (q : ℝ) ^ 2) := by
      dsimp [s]
      rw [Real.volume_pi_Ico]
      simp [Fin.prod_univ_two]
      rw [show ((z.1 : ℝ) + 1) / q - (z.1 : ℝ) / q = 1 / q by field_simp; ring,
        show ((z.2 : ℝ) + 1) / q - (z.2 : ℝ) / q = 1 / q by field_simp; ring]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (q : ℝ))]
      congr 1
      ring

/-- A cell point is within `2/q` of its midpoint. -/
theorem dist_gridMidpoint_lt {q : ℕ} (hq : 0 < q) {z : ℤ × ℤ} {x : Plane}
    (hx : x ∈ scaledCell q z) : dist x (gridMidpoint q z) < 2 / q := by
  rw [dist_eq_norm]
  have hqR : 0 < (q : ℝ) := by positivity
  have hz := mem_scaledCell.mp hx
  have hid0 : ((z.1 : ℝ) + 1 / 2) / q - (z.1 : ℝ) / q = 1 / (2 * q) := by
    field_simp
    ring
  have hid1 : ((z.1 : ℝ) + 1) / q - ((z.1 : ℝ) + 1 / 2) / q = 1 / (2 * q) := by
    field_simp
    ring
  have hhalf : 0 < 1 / (2 * (q : ℝ)) := by positivity
  have hhalf_lt : 1 / (2 * (q : ℝ)) < 1 / q := by
    field_simp [ne_of_gt hqR]
    norm_num
  have h0 : |x 0 - ((z.1 : ℝ) + 1 / 2) / q| < 1 / q := by
    rw [abs_lt]
    constructor <;> nlinarith [hz.1, hz.2.1, hid0, hid1]
  have hid2 : ((z.2 : ℝ) + 1 / 2) / q - (z.2 : ℝ) / q = 1 / (2 * q) := by
    field_simp
    ring
  have hid3 : ((z.2 : ℝ) + 1) / q - ((z.2 : ℝ) + 1 / 2) / q = 1 / (2 * q) := by
    field_simp
    ring
  have h1 : |x 1 - ((z.2 : ℝ) + 1 / 2) / q| < 1 / q := by
    rw [abs_lt]
    constructor <;> nlinarith [hz.2.2.1, hz.2.2.2, hid2, hid3]
  have h0sq : (x 0 - ((z.1 : ℝ) + 1 / 2) / q) ^ 2 < (1 / q) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) (by positivity)).2 h0
  have h1sq : (x 1 - ((z.2 : ℝ) + 1 / 2) / q) ^ 2 < (1 / q) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) (by positivity)).2 h1
  have hs : ‖x - gridMidpoint q z‖ ^ 2 < (2 / (q : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, PiLp.sub_apply, gridMidpoint,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hid : (2 / (q : ℝ)) ^ 2 = 4 * (1 / q) ^ 2 := by ring
    rw [hid]
    nlinarith
  have htwo : 0 < 2 / (q : ℝ) := by positivity
  nlinarith [norm_nonneg (x - gridMidpoint q z)]

end
end DiskDiscrepancy
