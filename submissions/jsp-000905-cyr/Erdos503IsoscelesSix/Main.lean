import Mathlib

/-!
# Erdős Problems #503 / #1088: a six-point planar set in which every triangle is isosceles

Erdős Problem #503 asks for the largest `A ⊆ ℝ^d` such that every three points of `A` determine
an isosceles triangle; for `d = 2` the answer is `6` (Erdős–Kelly 1947, AMM E735; Kelly's upper
bound, Kovács 2024 for an alternative proof).  Erdős Problem #1088 asks for `f_d(n)`, the least
`m` such that any `m` points in `ℝ^d` contain `n` points with pairwise distinct distances, and
records "Erdős could prove `f_2(3) = 7`".  This file proves the construction half of both facts:
the vertices of a regular pentagon together with its centre form a `6`-point set in the plane in
which every three points form an isosceles triangle.  Hence `6` is attained in #503 (`d = 2`) and
`f_2(3) ≥ 7` in #1088.  Kelly's matching upper bound (`|A| ≤ 6`, equivalently `f_2(3) ≤ 7`) and
everything else in #503/#1088 is OPEN or not addressed here.

The predicates `IsIsosceles`, `Set.Triplewise` and `Set.IsIsosceles` are copied verbatim from
the formal-conjectures repository (`FormalConjecturesForMathlib/Data/Set/Triplewise.lean` and
`FormalConjecturesForMathlib/Geometry/2d.lean`), and `ℝ²` is `EuclideanSpace ℝ (Fin 2)` as there,
so that the root theorem is the membership half of `Erdos503.erdos_503.variants.R2`
(`IsGreatest {(A.ncard) | (A : Set ℝ²) (hA : A.IsIsosceles)} 6`).
-/

open Real

/-- Three points form an isosceles triangle (formal-conjectures definition). -/
def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

/-- The ternary relation `r` holds triplewise on the set `s` (formal-conjectures definition). -/
protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

/-- Every three points of `A` form an isosceles triangle (formal-conjectures definition). -/
nonrec def Set.IsIsosceles {α : Type} [Dist α] (A : Set α) :=
  Nonempty A ∧ A.Triplewise (IsIsosceles · · ·)

/-- The `j`-th vertex of the regular pentagon inscribed in the unit circle. -/
noncomputable def pentagon (j : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * π * j / 5), Real.sin (2 * π * j / 5)]

/-- The centre of the pentagon. -/
noncomputable def centre : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]

/-- The six-point configuration: the five pentagon vertices and the centre. -/
noncomputable def sixPoints : Set (EuclideanSpace ℝ (Fin 2)) :=
  {centre, pentagon 0, pentagon 1, pentagon 2, pentagon 3, pentagon 4}

/-! ### Helper lemmas

Coordinates, the two pentagon distances, and the positivity facts needed below.  Nothing in this
section changes any definition or statement above.
-/

theorem pentagon_apply_zero (j : ℕ) : (pentagon j) 0 = Real.cos (2 * π * j / 5) := rfl

theorem pentagon_apply_one (j : ℕ) : (pentagon j) 1 = Real.sin (2 * π * j / 5) := rfl

theorem centre_apply_zero : centre 0 = 0 := rfl

theorem centre_apply_one : centre 1 = 0 := rfl

/-- The chord length between two pentagon vertices. -/
theorem dist_pentagon (i j : ℕ) : dist (pentagon i) (pentagon j)
    = √(2 - 2 * Real.cos (2 * π * i / 5 - 2 * π * j / 5)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  rw [Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs, pentagon_apply_zero, pentagon_apply_one, Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq (2 * π * i / 5), Real.sin_sq_add_cos_sq (2 * π * j / 5)]

/-- Every vertex lies on the unit circle centred at `centre`. -/
theorem dist_centre_pentagon (j : ℕ) : dist centre (pentagon j) = 1 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs, pentagon_apply_zero, pentagon_apply_one, centre_apply_zero,
    centre_apply_one, zero_sub, neg_sq]
  rw [Real.cos_sq_add_sin_sq]
  exact Real.sqrt_one

theorem dist_pentagon_centre (j : ℕ) : dist (pentagon j) centre = 1 := by
  rw [dist_comm]
  exact dist_centre_pentagon j

/-- Vertices at index gap `±1` (equivalently `±4`) are at the short chord distance. -/
theorem dist_pent_A (i j : ℕ)
    (h : (i : ℝ) - j = 1 ∨ (i : ℝ) - j = -1 ∨ (i : ℝ) - j = 4 ∨ (i : ℝ) - j = -4) :
    dist (pentagon i) (pentagon j) = √(2 - 2 * Real.cos (2 * π / 5)) := by
  rw [dist_pentagon]
  rcases h with h | h | h | h
  · rw [show 2 * π * (i : ℝ) / 5 - 2 * π * (j : ℝ) / 5 = 2 * π / 5 by
      linear_combination (2 * π / 5) * h]
  · rw [show 2 * π * (i : ℝ) / 5 - 2 * π * (j : ℝ) / 5 = -(2 * π / 5) by
      linear_combination (2 * π / 5) * h, Real.cos_neg]
  · rw [show 2 * π * (i : ℝ) / 5 - 2 * π * (j : ℝ) / 5 = 2 * π - 2 * π / 5 by
      linear_combination (2 * π / 5) * h, Real.cos_two_pi_sub]
  · rw [show 2 * π * (i : ℝ) / 5 - 2 * π * (j : ℝ) / 5 = -(2 * π - 2 * π / 5) by
      linear_combination (2 * π / 5) * h, Real.cos_neg, Real.cos_two_pi_sub]

/-- Vertices at index gap `±2` (equivalently `±3`) are at the long chord distance. -/
theorem dist_pent_B (i j : ℕ)
    (h : (i : ℝ) - j = 2 ∨ (i : ℝ) - j = -2 ∨ (i : ℝ) - j = 3 ∨ (i : ℝ) - j = -3) :
    dist (pentagon i) (pentagon j) = √(2 - 2 * Real.cos (4 * π / 5)) := by
  rw [dist_pentagon]
  rcases h with h | h | h | h
  · rw [show 2 * π * (i : ℝ) / 5 - 2 * π * (j : ℝ) / 5 = 4 * π / 5 by
      linear_combination (2 * π / 5) * h]
  · rw [show 2 * π * (i : ℝ) / 5 - 2 * π * (j : ℝ) / 5 = -(4 * π / 5) by
      linear_combination (2 * π / 5) * h, Real.cos_neg]
  · rw [show 2 * π * (i : ℝ) / 5 - 2 * π * (j : ℝ) / 5 = 2 * π - 4 * π / 5 by
      linear_combination (2 * π / 5) * h, Real.cos_two_pi_sub]
  · rw [show 2 * π * (i : ℝ) / 5 - 2 * π * (j : ℝ) / 5 = -(2 * π - 4 * π / 5) by
      linear_combination (2 * π / 5) * h, Real.cos_neg, Real.cos_two_pi_sub]

theorem dist_p01 : dist (pentagon 0) (pentagon 1) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 0 1 (by norm_num)

theorem dist_p02 : dist (pentagon 0) (pentagon 2) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 0 2 (by norm_num)

theorem dist_p03 : dist (pentagon 0) (pentagon 3) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 0 3 (by norm_num)

theorem dist_p04 : dist (pentagon 0) (pentagon 4) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 0 4 (by norm_num)

theorem dist_p10 : dist (pentagon 1) (pentagon 0) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 1 0 (by norm_num)

theorem dist_p12 : dist (pentagon 1) (pentagon 2) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 1 2 (by norm_num)

theorem dist_p13 : dist (pentagon 1) (pentagon 3) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 1 3 (by norm_num)

theorem dist_p14 : dist (pentagon 1) (pentagon 4) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 1 4 (by norm_num)

theorem dist_p20 : dist (pentagon 2) (pentagon 0) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 2 0 (by norm_num)

theorem dist_p21 : dist (pentagon 2) (pentagon 1) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 2 1 (by norm_num)

theorem dist_p23 : dist (pentagon 2) (pentagon 3) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 2 3 (by norm_num)

theorem dist_p24 : dist (pentagon 2) (pentagon 4) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 2 4 (by norm_num)

theorem dist_p30 : dist (pentagon 3) (pentagon 0) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 3 0 (by norm_num)

theorem dist_p31 : dist (pentagon 3) (pentagon 1) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 3 1 (by norm_num)

theorem dist_p32 : dist (pentagon 3) (pentagon 2) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 3 2 (by norm_num)

theorem dist_p34 : dist (pentagon 3) (pentagon 4) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 3 4 (by norm_num)

theorem dist_p40 : dist (pentagon 4) (pentagon 0) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 4 0 (by norm_num)

theorem dist_p41 : dist (pentagon 4) (pentagon 1) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 4 1 (by norm_num)

theorem dist_p42 : dist (pentagon 4) (pentagon 2) = √(2 - 2 * Real.cos (4 * π / 5)) :=
  dist_pent_B 4 2 (by norm_num)

theorem dist_p43 : dist (pentagon 4) (pentagon 3) = √(2 - 2 * Real.cos (2 * π / 5)) :=
  dist_pent_A 4 3 (by norm_num)

theorem cos_lt_one_of_mem_Ioo {x : ℝ} (h₁ : -(2 * π) < x) (h₂ : x < 2 * π) (h₀ : x ≠ 0) :
    Real.cos x < 1 :=
  lt_of_le_of_ne (Real.cos_le_one x) fun h => h₀ ((Real.cos_eq_one_iff_of_lt_of_lt h₁ h₂).1 h)

theorem shortChord_pos : 0 < √(2 - 2 * Real.cos (2 * π / 5)) := by
  have hpi := Real.pi_pos
  have : Real.cos (2 * π / 5) < 1 :=
    cos_lt_one_of_mem_Ioo (by linarith) (by linarith) (by positivity)
  exact Real.sqrt_pos.2 (by linarith)

theorem longChord_pos : 0 < √(2 - 2 * Real.cos (4 * π / 5)) := by
  have hpi := Real.pi_pos
  have : Real.cos (4 * π / 5) < 1 :=
    cos_lt_one_of_mem_Ioo (by linarith) (by linarith) (by positivity)
  exact Real.sqrt_pos.2 (by linarith)

theorem sixPoints_isIsosceles : sixPoints.IsIsosceles := by
  refine ⟨⟨⟨centre, by simp [sixPoints]⟩⟩, ?_⟩
  intro x hx y hy z hz hxy hyz hxz
  simp only [sixPoints, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  show dist x y = dist y z ∨ dist y z = dist z x ∨ dist z x = dist x y
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxy
          | exact absurd rfl hyz
          | exact absurd rfl hxz
          | simp only [dist_p01, dist_p02, dist_p03, dist_p04, dist_p10, dist_p12, dist_p13,
              dist_p14, dist_p20, dist_p21, dist_p23, dist_p24, dist_p30, dist_p31, dist_p32,
              dist_p34, dist_p40, dist_p41, dist_p42, dist_p43, dist_centre_pentagon,
              dist_pentagon_centre, true_or, or_true]

theorem sixPoints_ncard : sixPoints.ncard = 6 := by
  have hc : ∀ j : ℕ, centre ≠ pentagon j := fun j =>
    dist_ne_zero.1 (by rw [dist_centre_pentagon]; norm_num)
  have h01 : pentagon 0 ≠ pentagon 1 := dist_ne_zero.1 (by rw [dist_p01]; exact shortChord_pos.ne')
  have h02 : pentagon 0 ≠ pentagon 2 := dist_ne_zero.1 (by rw [dist_p02]; exact longChord_pos.ne')
  have h03 : pentagon 0 ≠ pentagon 3 := dist_ne_zero.1 (by rw [dist_p03]; exact longChord_pos.ne')
  have h04 : pentagon 0 ≠ pentagon 4 := dist_ne_zero.1 (by rw [dist_p04]; exact shortChord_pos.ne')
  have h12 : pentagon 1 ≠ pentagon 2 := dist_ne_zero.1 (by rw [dist_p12]; exact shortChord_pos.ne')
  have h13 : pentagon 1 ≠ pentagon 3 := dist_ne_zero.1 (by rw [dist_p13]; exact longChord_pos.ne')
  have h14 : pentagon 1 ≠ pentagon 4 := dist_ne_zero.1 (by rw [dist_p14]; exact longChord_pos.ne')
  have h23 : pentagon 2 ≠ pentagon 3 := dist_ne_zero.1 (by rw [dist_p23]; exact shortChord_pos.ne')
  have h24 : pentagon 2 ≠ pentagon 4 := dist_ne_zero.1 (by rw [dist_p24]; exact longChord_pos.ne')
  have h34 : pentagon 3 ≠ pentagon 4 := dist_ne_zero.1 (by rw [dist_p34]; exact shortChord_pos.ne')
  rw [sixPoints, Set.ncard_insert_of_notMem (by simp [hc]),
    Set.ncard_insert_of_notMem (by simp [h01, h02, h03, h04]),
    Set.ncard_insert_of_notMem (by simp [h12, h13, h14]),
    Set.ncard_insert_of_notMem (by simp [h23, h24]),
    Set.ncard_insert_of_notMem (by simp [h34]), Set.ncard_singleton]

/-- **Erdős #503 (`d = 2`), the construction half / Erdős #1088, `f_2(3) ≥ 7`.**  There is a
six-point subset of the plane in which every three points form an isosceles triangle.  Kelly's
upper bound `6` is not proved here. -/
theorem erdos_503_R2_six_point_isosceles_set :
    ∃ A : Set (EuclideanSpace ℝ (Fin 2)), A.IsIsosceles ∧ A.ncard = 6 :=
  ⟨sixPoints, sixPoints_isIsosceles, sixPoints_ncard⟩

-- The binder `hA` in the set-builder statement below is part of the frozen formal-conjectures
-- shape and is deliberately unnamed-but-present; silence the unused-variable linter for it.
set_option linter.unusedVariables false in
/-- The same fact in the exact shape of the formal-conjectures set
`{(A.ncard) | (A : Set ℝ²) (hA : A.IsIsosceles)}` used by `erdos_503.variants.R2`. -/
theorem six_mem_isosceles_ncards :
    6 ∈ {(A.ncard) | (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : A.IsIsosceles)} := by
  obtain ⟨A, hA, hc⟩ := erdos_503_R2_six_point_isosceles_set
  exact ⟨A, hA, hc⟩

/-- Consequence for Erdős #1088 (`d = 2`, `n = 3`): there are six points of the plane no three of
which have pairwise distinct distances, so `f_2(3) ≥ 7`. -/
theorem exists_six_points_no_three_distinct_distances :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = 6 ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
        ¬ (dist x y ≠ dist y z ∧ dist y z ≠ dist z x ∧ dist z x ≠ dist x y) := by
  classical
  have hfin : sixPoints.Finite := by unfold sixPoints; exact Set.toFinite _
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card sixPoints hfin]
    exact sixPoints_ncard
  · intro x hx y hy z hz hxy hyz hxz
    rw [Set.Finite.mem_toFinset] at hx hy hz
    have h : dist x y = dist y z ∨ dist y z = dist z x ∨ dist z x = dist x y :=
      sixPoints_isIsosceles.2 hx hy hz hxy hyz hxz
    rintro ⟨h1, h2, h3⟩
    rcases h with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
