import Mathlib

/-!
# Erdős Problem #508 (Hadwiger–Nelson): the chromatic number of the plane is at least `4`

The Hadwiger–Nelson problem asks for the chromatic number `χ(ℝ²)` of the plane: the least number
of colours needed to colour `ℝ²` so that no two points at distance `1` receive the same colour.
The problem is OPEN; the best known bounds are `5 ≤ χ(ℝ²) ≤ 7` (de Grey 2018 for the lower
bound).  This file proves the classical, now superseded, lower bound `χ(ℝ²) ≥ 4` by the
Moser spindle (Moser–Moser 1961): seven points forming two unit rhombi `A B C D`, `A B' C' D'`
with a common vertex `A`, the second obtained from the first by the rotation with
`cos θ = 5/6`, `sin θ = √11/6`, so that `|D D'| = 1`; the resulting unit-distance graph has
`11` edges and no proper `3`-colouring.

The graph `UnitDistancePlaneGraph` and the statement `4 ≤ χ(ℝ²)` are those of the
formal-conjectures file `Erdos508` (`HadwigerNelsonAtLeast4`, tagged "research solved" with
`sorry`).  Neither de Grey's bound `χ(ℝ²) ≥ 5` nor the value of `χ(ℝ²)` is claimed here.
-/

/-- A unit distance graph in `ℝ²`: the vertices are a collection of points in `ℝ²`, and two
points are adjacent if and only if their distance is `1` (formal-conjectures definition). -/
def UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := dist x y = 1
  symm.symm x y := by simp [dist_comm]

open SimpleGraph

/-- The seven vertices of the Moser spindle: `A, B, C, D` form a unit rhombus (two equilateral
triangles `ABC`, `BCD`), and `B', C', D'` are the images of `B, C, D` under the rotation about `A`
with `cos θ = 5/6`, `sin θ = √11/6`, chosen so that `dist D D' = 1`. -/
noncomputable def moser : Fin 7 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0],
    !₂[1, 0],
    !₂[1 / 2, Real.sqrt 3 / 2],
    !₂[3 / 2, Real.sqrt 3 / 2],
    !₂[5 / 6, Real.sqrt 11 / 6],
    !₂[5 / 12 - Real.sqrt 3 * Real.sqrt 11 / 12, Real.sqrt 11 / 12 + 5 * Real.sqrt 3 / 12],
    !₂[5 / 4 - Real.sqrt 3 * Real.sqrt 11 / 12, Real.sqrt 11 / 4 + 5 * Real.sqrt 3 / 12]]

/-- The eleven unit edges of the Moser spindle (as index pairs into `moser`). -/
def moserEdges : List (Fin 7 × Fin 7) :=
  [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (0, 4), (0, 5), (4, 5), (4, 6), (5, 6), (3, 6)]

/-- Auxiliary: the squared-distance criterion for two points of `ℝ²` given in coordinates. -/
private theorem dist_pair_eq_one {a b c d : ℝ} (h : (a - c) ^ 2 + (b - d) ^ 2 = 1) :
    dist (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) !₂[c, d] = 1 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp, EuclideanSpace.dist_eq]
  congr 1
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  linarith [h]

/-- Every listed edge of the spindle has length `1`. -/
theorem moser_dist_eq_one : ∀ e ∈ moserEdges, dist (moser e.1) (moser e.2) = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  intro e he
  fin_cases he <;>
    simp only [moser, Matrix.cons_val] <;>
    apply dist_pair_eq_one <;>
    nlinarith [h3, h11]

set_option maxRecDepth 10000

/-- The abstract Moser spindle has no proper `3`-colouring: every `f : Fin 7 → Fin 3` is
constant on some listed edge. -/
theorem moser_no_three_colouring (f : Fin 7 → Fin 3) : ∃ e ∈ moserEdges, f e.1 = f e.2 := by
  revert f
  decide

/-- **Erdős #508, the classical lower bound (Moser spindle).**  The unit-distance graph of the
plane has chromatic number at least `4`, in the formal-conjectures shape
`4 ≤ SimpleGraph.chromaticNumber (UnitDistancePlaneGraph Set.univ)`.  The value of `χ(ℝ²)` and
de Grey's bound `≥ 5` are not addressed. -/
theorem hadwiger_nelson_at_least_four :
    4 ≤ (UnitDistancePlaneGraph Set.univ).chromaticNumber := by
  by_contra hlt
  rw [not_le] at hlt
  have hle : (UnitDistancePlaneGraph Set.univ).chromaticNumber ≤ ((3 : ℕ) : ℕ∞) := by
    exact_mod_cast Order.le_of_lt_succ hlt
  obtain ⟨C⟩ := chromaticNumber_le_iff_colorable.mp hle
  obtain ⟨e, he, hfe⟩ :=
    moser_no_three_colouring (fun i => C ⟨moser i, Set.mem_univ _⟩)
  have hadj : (UnitDistancePlaneGraph Set.univ).Adj
      ⟨moser e.1, Set.mem_univ _⟩ ⟨moser e.2, Set.mem_univ _⟩ := by
    show dist (⟨moser e.1, Set.mem_univ _⟩ : (Set.univ : Set (EuclideanSpace ℝ (Fin 2))))
      ⟨moser e.2, Set.mem_univ _⟩ = 1
    rw [Subtype.dist_eq]
    exact moser_dist_eq_one e he
  exact C.valid hadj hfe
