import Mathlib

/-!
# Erdős Problem #661: Lenz's construction in `ℝ^4`

Erdős asked whether for all large `n` there are points `x_1, …, x_n, y_1, …, y_n ∈ ℝ^2` with
`o(n / √(log n))` distinct distances `d(x_i, y_j)` (OPEN, $50; not addressed here).  The problem
page records: "In `ℝ^4` Lenz observed that there are `x_1, …, x_n, y_1, …, y_n ∈ ℝ^4` such that
`d(x_i, y_j) = 1` for all `i, j`, taking the points on two orthogonal circles."  This file proves
Lenz's observation for every `n`: with `x_i = (cos θ_i, sin θ_i, 0, 0) / √2` and
`y_j = (0, 0, cos φ_j, sin φ_j) / √2` (the `x_i` on the circle of radius `1/√2` in the first
coordinate plane, the `y_j` on the orthogonal circle in the last two coordinates, distinct angles
in `[0, π)`), every distance `d(x_i, y_j)` equals `√(1/2 + 1/2) = 1`, and the `2n` points are
pairwise distinct.  There is no formal-conjectures rendering of this problem; the statement is
ours, in `EuclideanSpace ℝ (Fin 4)` with its Euclidean distance.
-/

namespace Erdos661

/-- The `x`-points: on the circle of radius `1/√2` in the plane of the first two coordinates. -/
noncomputable def xPt (n i : ℕ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[Real.cos (i * Real.pi / n) / Real.sqrt 2, Real.sin (i * Real.pi / n) / Real.sqrt 2, 0, 0]

/-- The `y`-points: on the orthogonal circle of radius `1/√2` in the plane of the last two
coordinates. -/
noncomputable def yPt (n j : ℕ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[0, 0, Real.cos (j * Real.pi / n) / Real.sqrt 2, Real.sin (j * Real.pi / n) / Real.sqrt 2]

/-- The angle `i π / n` attached to an index `i < n` lies in `[0, π]`. -/
theorem angle_mem_Icc (n : ℕ) (i : Fin n) :
    ((i : ℕ) : ℝ) * Real.pi / n ∈ Set.Icc 0 Real.pi := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  have hle : ((i : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt i.isLt
  constructor
  · positivity
  · rw [div_le_iff₀ hn]
    nlinarith [Real.pi_pos]

/-- Distinct indices `i < n` give distinct angles `i π / n`. -/
theorem angle_inj (n : ℕ) (i j : Fin n)
    (h : ((i : ℕ) : ℝ) * Real.pi / n = ((j : ℕ) : ℝ) * Real.pi / n) : i = j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  have hpi := Real.pi_ne_zero
  field_simp at h
  exact Fin.ext (by exact_mod_cast h)

/-- Since the angles `i π / n` for `i < n` lie in `[0, π]`, where `cos` is injective, equality of
the scaled cosines forces equality of the indices. -/
theorem eq_of_cos_div_sqrt_two_eq (n : ℕ) (i j : Fin n)
    (h : Real.cos (((i : ℕ) : ℝ) * Real.pi / n) / Real.sqrt 2
      = Real.cos (((j : ℕ) : ℝ) * Real.pi / n) / Real.sqrt 2) : i = j := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  exact angle_inj n i j
    (Real.injOn_cos (angle_mem_Icc n i) (angle_mem_Icc n j) ((div_left_inj' h2).mp h))

/-- Every `x`-point is at distance `1` from every `y`-point. -/
theorem dist_xPt_yPt (n i j : ℕ) : dist (xPt n i) (yPt n j) = 1 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hi := Real.sin_sq_add_cos_sq (i * Real.pi / n)
  have hj := Real.sin_sq_add_cos_sq (j * Real.pi / n)
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_four, Real.sqrt_eq_one]
  simp only [xPt, yPt, Real.dist_eq, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    sub_zero, zero_sub, neg_sq, div_pow, hs]
  linarith

/-- The `x`-points with indices `0 ≤ i < n` are pairwise distinct (angles in `[0, π)`). -/
theorem xPt_injective (n : ℕ) : Function.Injective (fun i : Fin n => xPt n i) := by
  intro i j h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v 0) h
  simp only [xPt, Matrix.cons_val_zero] at h0
  exact eq_of_cos_div_sqrt_two_eq n i j h0

/-- The `y`-points with indices `0 ≤ j < n` are pairwise distinct. -/
theorem yPt_injective (n : ℕ) : Function.Injective (fun j : Fin n => yPt n j) := by
  intro i j h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v 2) h
  simp only [yPt, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h0
  exact eq_of_cos_div_sqrt_two_eq n i j h0

/-- No `x`-point coincides with a `y`-point (they are at distance `1`). -/
theorem xPt_ne_yPt (n i j : ℕ) : xPt n i ≠ yPt n j := by
  intro h
  have hd := dist_xPt_yPt n i j
  rw [h, dist_self] at hd
  norm_num at hd

end Erdos661

open Erdos661 in
/-- **Erdős #661, Lenz's observation**: for every `n` there are `2n` distinct points
`x_1, …, x_n, y_1, …, y_n ∈ ℝ^4` with `d(x_i, y_j) = 1` for all `i, j`. -/
theorem erdos_661_lenz (n : ℕ) :
    ∃ x y : Fin n → EuclideanSpace ℝ (Fin 4), Function.Injective x ∧ Function.Injective y ∧
      (∀ i j, x i ≠ y j) ∧ ∀ i j, dist (x i) (y j) = 1 := by
  exact ⟨fun i => xPt n i, fun j => yPt n j, xPt_injective n, yPt_injective n,
    fun i j => xPt_ne_yPt n i j, fun i j => dist_xPt_yPt n i j⟩
