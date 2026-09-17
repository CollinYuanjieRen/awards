import Jsp202.DiameterGraph

/-!
# Lower-bound constructions for the planar diameter problem (Hopf–Pannwitz / Erdős #223)

Explicit planar point configurations witnessing that the maximum number of *diameter pairs*
among `n` points is at least `n` (the easy direction `f₂(n) ≥ n`), for `n = 3, 4, 5`.

* `f2_three` — the equilateral triangle: `3` points, `3` diameter pairs (the complete graph `K₃`).
* `f2_four`  — equilateral triangle plus one point at distance `1` from a single vertex: `4` pairs.
* `f2_five`  — equilateral triangle plus two points at distance `1` from a single vertex: `5` pairs.

In each case the diameter graph `diameterGraph P D` (adjacency `dist (P i) (P j) = D`, from
`Jsp202.DiameterGraph`) is shown to have exactly `n` edges, with all pairwise distances `≤ D = 1`.
-/

open scoped Classical

namespace HopfPannwitz

/-- Distance formula for two explicit points of `EuclideanSpace ℝ (Fin 2)` written with the
`!₂[·,·]` notation. -/
theorem dist_pt (a b c d : ℝ) :
    dist (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) (!₂[c, d]) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]

/-! ## `n = 3` — the equilateral triangle -/

noncomputable def triP : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]]

/-- Every pair of distinct vertices of `triP` is at distance exactly `1`. -/
theorem tri_dist : ∀ i j : Fin 3, i ≠ j → dist (triP i) (triP j) = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have d01 : dist (triP 0) (triP 1) = 1 := by
    simp only [triP, Matrix.cons_val_zero, Matrix.cons_val_one, dist_pt]
    norm_num
  have d02 : dist (triP 0) (triP 2) = 1 := by
    simp only [triP, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, dist_pt]
    rw [show ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = Real.sqrt 3 ^ 2 / 4 by ring, h3,
        show ((0 : ℝ) - 1 / 2) ^ 2 + 3 / 4 = 1 by ring, Real.sqrt_one]
  have d12 : dist (triP 1) (triP 2) = 1 := by
    simp only [triP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, dist_pt]
    rw [show ((0 : ℝ) - Real.sqrt 3 / 2) ^ 2 = Real.sqrt 3 ^ 2 / 4 by ring, h3,
        show ((1 : ℝ) - 1 / 2) ^ 2 + 3 / 4 = 1 by ring, Real.sqrt_one]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact d01
      | exact d02
      | exact d12
      | (rw [dist_comm]; exact d01)
      | (rw [dist_comm]; exact d02)
      | (rw [dist_comm]; exact d12)

/-- **`f₂(3) ≥ 3`.** The equilateral triangle: three planar points, pairwise distances `≤ 1`,
whose diameter graph (distance `= 1`) has exactly `3` edges. -/
theorem f2_three :
    ∃ (P : Fin 3 → EuclideanSpace ℝ (Fin 2)) (D : ℝ),
      Function.Injective P ∧ (∀ i j, dist (P i) (P j) ≤ D) ∧
      (diameterGraph P D).edgeFinset.card = 3 := by
  refine ⟨triP, 1, ?_, ?_, ?_⟩
  · -- injectivity
    intro i j hPij
    by_contra hne
    have := tri_dist i j hne
    rw [hPij, dist_self] at this
    norm_num at this
  · -- all distances ≤ 1
    intro i j
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [tri_dist i j h]
  · -- the diameter graph is complete on `3` vertices, hence has `3.choose 2 = 3` edges
    have htop : diameterGraph triP 1 = ⊤ := by
      ext i j
      simp only [diameterGraph, SimpleGraph.top_adj]
      exact ⟨fun h => h.1, fun h => ⟨h, tri_dist i j h⟩⟩
    have hEF : (diameterGraph triP 1).edgeFinset = (⊤ : SimpleGraph (Fin 3)).edgeFinset := by
      ext e; simp only [SimpleGraph.mem_edgeFinset, htop]
    rw [hEF, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    decide

/-! ## `n = 4` — equilateral triangle plus one apex point -/

noncomputable def fourP : Fin 4 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2], !₂[Real.sqrt 3 / 2, 1 / 2]]

def r4 (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 3)
instance : DecidableRel r4 := fun i j => by unfold r4; infer_instance

theorem four_facts : Real.sqrt 3 ^ 2 = 3 ∧ (1:ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 2 := by
  refine ⟨Real.sq_sqrt (by norm_num), ?_, ?_⟩
  · have : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using this
  · have h4 : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at h4

theorem e01 : dist (fourP 0) (fourP 1) = 1 := by
  simp only [fourP, Matrix.cons_val_zero, Matrix.cons_val_one, dist_pt]; norm_num
theorem e02 : dist (fourP 0) (fourP 2) = 1 := by
  obtain ⟨h3, _, _⟩ := four_facts
  simp only [fourP, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, dist_pt]
  rw [show ((0:ℝ)-1/2)^2 + (0-Real.sqrt 3/2)^2 = Real.sqrt 3^2/4 + 1/4 by ring, h3,
      show (3:ℝ)/4 + 1/4 = 1 by norm_num, Real.sqrt_one]
theorem e03 : dist (fourP 0) (fourP 3) = 1 := by
  obtain ⟨h3, _, _⟩ := four_facts
  simp only [fourP, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_three, Matrix.tail_cons, dist_pt]
  rw [show ((0:ℝ)-Real.sqrt 3/2)^2 + (0-1/2)^2 = Real.sqrt 3^2/4 + 1/4 by ring, h3,
      show (3:ℝ)/4 + 1/4 = 1 by norm_num, Real.sqrt_one]
theorem e12 : dist (fourP 1) (fourP 2) = 1 := by
  obtain ⟨h3, _, _⟩ := four_facts
  simp only [fourP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, dist_pt]
  rw [show ((1:ℝ)-1/2)^2 + (0-Real.sqrt 3/2)^2 = Real.sqrt 3^2/4 + 1/4 by ring, h3,
      show (3:ℝ)/4 + 1/4 = 1 by norm_num, Real.sqrt_one]
theorem v13 : dist (fourP 1) (fourP 3) = Real.sqrt (2 - Real.sqrt 3) := by
  obtain ⟨h3, _, _⟩ := four_facts
  simp only [fourP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_three, Matrix.tail_cons, dist_pt]
  congr 1; linear_combination (1/4) * h3
theorem v23 : dist (fourP 2) (fourP 3) = Real.sqrt (2 - Real.sqrt 3) := by
  obtain ⟨h3, _, _⟩ := four_facts
  simp only [fourP, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, dist_pt]
  congr 1; linear_combination (1/2) * h3

theorem sq_lt : (0:ℝ) < 2 - Real.sqrt 3 ∧ (2 - Real.sqrt 3) < 1 := by
  obtain ⟨_, h1, h2⟩ := four_facts; exact ⟨by nlinarith, by nlinarith⟩
theorem nd_pos : Real.sqrt (2 - Real.sqrt 3) ≠ 0 :=
  Real.sqrt_ne_zero'.mpr sq_lt.1
theorem nd_lt1 : Real.sqrt (2 - Real.sqrt 3) ≠ 1 := by
  intro hc
  have := Real.sq_sqrt (le_of_lt sq_lt.1)
  rw [hc] at this; obtain ⟨_, _, h2⟩ := four_facts; nlinarith
theorem nd_le1 : Real.sqrt (2 - Real.sqrt 3) ≤ 1 := by
  rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (le_of_lt sq_lt.2)

theorem f2_four :
    ∃ (P : Fin 4 → EuclideanSpace ℝ (Fin 2)) (D : ℝ),
      Function.Injective P ∧ (∀ i j, dist (P i) (P j) ≤ D) ∧
      (diameterGraph P D).edgeFinset.card = 4 := by
  have e10 : dist (fourP 1) (fourP 0) = 1 := by rw [dist_comm]; exact e01
  have e20 : dist (fourP 2) (fourP 0) = 1 := by rw [dist_comm]; exact e02
  have e30 : dist (fourP 3) (fourP 0) = 1 := by rw [dist_comm]; exact e03
  have e21 : dist (fourP 2) (fourP 1) = 1 := by rw [dist_comm]; exact e12
  have v31 : dist (fourP 3) (fourP 1) = Real.sqrt (2 - Real.sqrt 3) := by rw [dist_comm]; exact v13
  have v32 : dist (fourP 3) (fourP 2) = Real.sqrt (2 - Real.sqrt 3) := by rw [dist_comm]; exact v23
  refine ⟨fourP, 1, ?_, ?_, ?_⟩
  · -- injective
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd (e01.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (e02.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (e03.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (e12.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (e10.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (e20.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (e30.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (e21.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (v13.symm.trans (dist_eq_zero.mpr hij)) nd_pos
        | exact absurd (v23.symm.trans (dist_eq_zero.mpr hij)) nd_pos
        | exact absurd (v31.symm.trans (dist_eq_zero.mpr hij)) nd_pos
        | exact absurd (v32.symm.trans (dist_eq_zero.mpr hij)) nd_pos
  · -- all distances ≤ 1
    intro i j
    fin_cases i <;> fin_cases j <;>
      first
        | exact (dist_self _).le.trans (by norm_num)
        | exact le_of_eq e01 | exact le_of_eq e02 | exact le_of_eq e03 | exact le_of_eq e12
        | exact le_of_eq e10 | exact le_of_eq e20 | exact le_of_eq e30 | exact le_of_eq e21
        | exact v13.le.trans nd_le1 | exact v23.le.trans nd_le1
        | exact v31.le.trans nd_le1 | exact v32.le.trans nd_le1
  · -- exactly 4 diameter pairs
    have hG : diameterGraph fourP 1 = SimpleGraph.fromRel r4 := by
      ext i j
      simp only [diameterGraph, SimpleGraph.fromRel_adj]
      fin_cases i <;> fin_cases j <;>
        first
          | exact iff_of_false (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
          | exact iff_of_true ⟨by decide, e01⟩ (by decide)
          | exact iff_of_true ⟨by decide, e02⟩ (by decide)
          | exact iff_of_true ⟨by decide, e03⟩ (by decide)
          | exact iff_of_true ⟨by decide, e12⟩ (by decide)
          | exact iff_of_true ⟨by decide, e10⟩ (by decide)
          | exact iff_of_true ⟨by decide, e20⟩ (by decide)
          | exact iff_of_true ⟨by decide, e30⟩ (by decide)
          | exact iff_of_true ⟨by decide, e21⟩ (by decide)
          | exact iff_of_false (fun h => nd_lt1 (v13.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => nd_lt1 (v23.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => nd_lt1 (v31.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => nd_lt1 (v32.symm.trans h.2)) (by decide)
    have hEF : (diameterGraph fourP 1).edgeFinset = (SimpleGraph.fromRel r4).edgeFinset := by
      ext e; simp only [SimpleGraph.mem_edgeFinset, hG]
    rw [hEF]; decide

/-! ## `n = 5` — equilateral triangle plus two apex points -/

theorem sqrt3_facts : Real.sqrt 3 ^ 2 = 3 ∧ (1:ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 7/4 := by
  refine ⟨Real.sq_sqrt (by norm_num), ?_, ?_⟩
  · have : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using this
  · have h4 : Real.sqrt 3 < Real.sqrt (49/16) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show (49/16:ℝ) = (7/4)^2 by norm_num, Real.sqrt_sq (by norm_num)] at h4

theorem sqrt_props {k : ℝ} (h0 : 0 < k) (h1 : k < 1) :
    Real.sqrt k ≤ 1 ∧ Real.sqrt k ≠ 1 ∧ Real.sqrt k ≠ 0 := by
  refine ⟨?_, ?_, Real.sqrt_ne_zero'.mpr h0⟩
  · rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (le_of_lt h1)
  · intro hc; have := Real.sq_sqrt h0.le; rw [hc] at this; norm_num at this; linarith

noncomputable def fiveP : Fin 5 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2], !₂[4/5, 3/5], !₂[3/5, 4/5]]

def r5 (i j : Fin 5) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4)
instance : DecidableRel r5 := fun i j => by unfold r5; infer_instance

-- edges = 1
theorem q01 : dist (fiveP 0) (fiveP 1) = 1 := by
  simp only [fiveP, Matrix.cons_val_zero, Matrix.cons_val_one, dist_pt]; norm_num
theorem q02 : dist (fiveP 0) (fiveP 2) = 1 := by
  obtain ⟨h3, _, _⟩ := sqrt3_facts
  simp only [fiveP, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, dist_pt]
  rw [show ((0:ℝ)-1/2)^2 + (0-Real.sqrt 3/2)^2 = Real.sqrt 3^2/4 + 1/4 by ring, h3,
      show (3:ℝ)/4 + 1/4 = 1 by norm_num, Real.sqrt_one]
theorem q12 : dist (fiveP 1) (fiveP 2) = 1 := by
  obtain ⟨h3, _, _⟩ := sqrt3_facts
  simp only [fiveP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, dist_pt]
  rw [show ((1:ℝ)-1/2)^2 + (0-Real.sqrt 3/2)^2 = Real.sqrt 3^2/4 + 1/4 by ring, h3,
      show (3:ℝ)/4 + 1/4 = 1 by norm_num, Real.sqrt_one]
theorem q03 : dist (fiveP 0) (fiveP 3) = 1 := by
  simp only [fiveP, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_three, Matrix.tail_cons, dist_pt]
  rw [show ((0:ℝ)-4/5)^2 + (0-3/5)^2 = 1 by norm_num, Real.sqrt_one]
theorem q04 : dist (fiveP 0) (fiveP 4) = 1 := by
  simp only [fiveP, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_four, Matrix.tail_cons, dist_pt]
  rw [show ((0:ℝ)-3/5)^2 + (0-4/5)^2 = 1 by norm_num, Real.sqrt_one]

-- non-edge values = sqrt k, 0 ≤ k < 1
theorem w13 : dist (fiveP 1) (fiveP 3) = Real.sqrt (2/5) := by
  simp only [fiveP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_three, Matrix.tail_cons, dist_pt]
  congr 1; norm_num
theorem w14 : dist (fiveP 1) (fiveP 4) = Real.sqrt (4/5) := by
  simp only [fiveP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_four, Matrix.tail_cons, dist_pt]
  congr 1; norm_num
theorem w34 : dist (fiveP 3) (fiveP 4) = Real.sqrt (2/25) := by
  simp only [fiveP, Matrix.head_cons,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, dist_pt]
  congr 1; norm_num
theorem w23 : dist (fiveP 2) (fiveP 3) = Real.sqrt ((6 - 3 * Real.sqrt 3)/5) := by
  obtain ⟨h3, _, _⟩ := sqrt3_facts
  simp only [fiveP, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, dist_pt]
  congr 1; linear_combination (1/4) * h3
theorem w24 : dist (fiveP 2) (fiveP 4) = Real.sqrt ((7 - 4 * Real.sqrt 3)/5) := by
  obtain ⟨h3, _, _⟩ := sqrt3_facts
  simp only [fiveP, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_four, Matrix.tail_cons, dist_pt]
  congr 1; linear_combination (1/4) * h3

-- k-bounds
theorem k13 : (0:ℝ) < 2/5 ∧ (2/5:ℝ) < 1 := ⟨by norm_num, by norm_num⟩
theorem k14 : (0:ℝ) < 4/5 ∧ (4/5:ℝ) < 1 := ⟨by norm_num, by norm_num⟩
theorem k34 : (0:ℝ) < 2/25 ∧ (2/25:ℝ) < 1 := ⟨by norm_num, by norm_num⟩
theorem k23 : (0:ℝ) < (6 - 3*Real.sqrt 3)/5 ∧ ((6 - 3*Real.sqrt 3)/5) < 1 := by
  obtain ⟨_, h1, h2⟩ := sqrt3_facts; exact ⟨by nlinarith, by nlinarith⟩
theorem k24 : (0:ℝ) < (7 - 4*Real.sqrt 3)/5 ∧ ((7 - 4*Real.sqrt 3)/5) < 1 := by
  obtain ⟨_, h1, h2⟩ := sqrt3_facts; exact ⟨by nlinarith, by nlinarith⟩
set_option maxHeartbeats 1000000 in
theorem f2_five :
    ∃ (P : Fin 5 → EuclideanSpace ℝ (Fin 2)) (D : ℝ),
      Function.Injective P ∧ (∀ i j, dist (P i) (P j) ≤ D) ∧
      (diameterGraph P D).edgeFinset.card = 5 := by
  -- reversed edges
  have q10 : dist (fiveP 1) (fiveP 0) = 1 := by rw [dist_comm]; exact q01
  have q20 : dist (fiveP 2) (fiveP 0) = 1 := by rw [dist_comm]; exact q02
  have q21 : dist (fiveP 2) (fiveP 1) = 1 := by rw [dist_comm]; exact q12
  have q30 : dist (fiveP 3) (fiveP 0) = 1 := by rw [dist_comm]; exact q03
  have q40 : dist (fiveP 4) (fiveP 0) = 1 := by rw [dist_comm]; exact q04
  -- reversed nonedge values
  have w31 : dist (fiveP 3) (fiveP 1) = Real.sqrt (2/5) := by rw [dist_comm]; exact w13
  have w41 : dist (fiveP 4) (fiveP 1) = Real.sqrt (4/5) := by rw [dist_comm]; exact w14
  have w43 : dist (fiveP 4) (fiveP 3) = Real.sqrt (2/25) := by rw [dist_comm]; exact w34
  have w32 : dist (fiveP 3) (fiveP 2) = Real.sqrt ((6 - 3 * Real.sqrt 3)/5) := by
    rw [dist_comm]; exact w23
  have w42 : dist (fiveP 4) (fiveP 2) = Real.sqrt ((7 - 4 * Real.sqrt 3)/5) := by
    rw [dist_comm]; exact w24
  have s13 := sqrt_props k13.1 k13.2
  have s14 := sqrt_props k14.1 k14.2
  have s34 := sqrt_props k34.1 k34.2
  have s23 := sqrt_props k23.1 k23.2
  have s24 := sqrt_props k24.1 k24.2
  refine ⟨fiveP, 1, ?_, ?_, ?_⟩
  · -- injective
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd (q01.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (q02.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (q12.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (q03.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (q04.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (q10.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (q20.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (q21.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (q30.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (q40.symm.trans (dist_eq_zero.mpr hij)) (by norm_num)
        | exact absurd (w13.symm.trans (dist_eq_zero.mpr hij)) s13.2.2
        | exact absurd (w14.symm.trans (dist_eq_zero.mpr hij)) s14.2.2
        | exact absurd (w34.symm.trans (dist_eq_zero.mpr hij)) s34.2.2
        | exact absurd (w23.symm.trans (dist_eq_zero.mpr hij)) s23.2.2
        | exact absurd (w24.symm.trans (dist_eq_zero.mpr hij)) s24.2.2
        | exact absurd (w31.symm.trans (dist_eq_zero.mpr hij)) s13.2.2
        | exact absurd (w41.symm.trans (dist_eq_zero.mpr hij)) s14.2.2
        | exact absurd (w43.symm.trans (dist_eq_zero.mpr hij)) s34.2.2
        | exact absurd (w32.symm.trans (dist_eq_zero.mpr hij)) s23.2.2
        | exact absurd (w42.symm.trans (dist_eq_zero.mpr hij)) s24.2.2
  · -- ≤ 1
    intro i j
    fin_cases i <;> fin_cases j <;>
      first
        | exact (dist_self _).le.trans (by norm_num)
        | exact le_of_eq q01 | exact le_of_eq q02 | exact le_of_eq q12
        | exact le_of_eq q03 | exact le_of_eq q04
        | exact le_of_eq q10 | exact le_of_eq q20 | exact le_of_eq q21
        | exact le_of_eq q30 | exact le_of_eq q40
        | exact w13.le.trans s13.1
        | exact w14.le.trans s14.1
        | exact w34.le.trans s34.1
        | exact w23.le.trans s23.1
        | exact w24.le.trans s24.1
        | exact w31.le.trans s13.1
        | exact w41.le.trans s14.1
        | exact w43.le.trans s34.1
        | exact w32.le.trans s23.1
        | exact w42.le.trans s24.1
  · -- exactly 5 diameter pairs
    have hG : diameterGraph fiveP 1 = SimpleGraph.fromRel r5 := by
      ext i j
      simp only [diameterGraph, SimpleGraph.fromRel_adj]
      fin_cases i <;> fin_cases j <;>
        first
          | exact iff_of_false (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
          | exact iff_of_true ⟨by decide, q01⟩ (by decide)
          | exact iff_of_true ⟨by decide, q02⟩ (by decide)
          | exact iff_of_true ⟨by decide, q12⟩ (by decide)
          | exact iff_of_true ⟨by decide, q03⟩ (by decide)
          | exact iff_of_true ⟨by decide, q04⟩ (by decide)
          | exact iff_of_true ⟨by decide, q10⟩ (by decide)
          | exact iff_of_true ⟨by decide, q20⟩ (by decide)
          | exact iff_of_true ⟨by decide, q21⟩ (by decide)
          | exact iff_of_true ⟨by decide, q30⟩ (by decide)
          | exact iff_of_true ⟨by decide, q40⟩ (by decide)
          | exact iff_of_false (fun h => s13.2.1 (w13.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => s14.2.1 (w14.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => s34.2.1 (w34.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => s23.2.1 (w23.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => s24.2.1 (w24.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => s13.2.1 (w31.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => s14.2.1 (w41.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => s34.2.1 (w43.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => s23.2.1 (w32.symm.trans h.2)) (by decide)
          | exact iff_of_false (fun h => s24.2.1 (w42.symm.trans h.2)) (by decide)
    have hEF : (diameterGraph fiveP 1).edgeFinset = (SimpleGraph.fromRel r5).edgeFinset := by
      ext e; simp only [SimpleGraph.mem_edgeFinset, hG]
    rw [hEF]; decide

#print axioms f2_three
#print axioms f2_four
#print axioms f2_five

end HopfPannwitz
