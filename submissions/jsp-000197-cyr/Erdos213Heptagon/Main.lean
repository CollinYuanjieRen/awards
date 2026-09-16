import Mathlib

/-!
# Erdős Problem #213: the Kreisel–Kurz integral heptagon in general position

Erdős asked (for `n ≥ 4`) whether there are `n` points in the plane, no three on a line and no four
on a circle, with all pairwise distances integers.  The problem is OPEN for `n ≥ 8`; Anning–Erdős
showed no infinite such set exists, Harborth found `n = 5`, and the best construction to date,
due to Kreisel and Kurz (2008), has `n = 7`.  This file certifies that construction: seven points
`(xᵢ, yᵢ √2002)` with rational `xᵢ, yᵢ` (Kreisel–Kurz, Fig. 1, characteristic `2002`), all `21`
distances integers, no three collinear and no four concyclic.

The predicate `Erdos213For` and the helper `NonTrilinear` / `Set.Triplewise` are copied verbatim
from the formal-conjectures repository (`ErdosProblems/213.lean`, `Geometry/2d.lean`,
`Data/Set/Triplewise.lean`; `ℝ²` there is `EuclideanSpace ℝ (Fin 2)`), so the root theorem is
exactly `Erdos213.erdos_213.variants.KK08 : Erdos213For 7` (tagged "research solved" with `sorry`).
Nothing is claimed for `n ≥ 8`, and nothing about the upper bounds (Ascher–Braune–Turchet,
Greenfeld–Iliopoulou–Peluse) is addressed.
-/

/-- The ternary relation `r` holds triplewise on the set `s` (formal-conjectures definition). -/
protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

/-- We say a subset `A` of points in the plane is non-trilinear
if it contains no three points that lie on the same line (formal-conjectures definition). -/
def NonTrilinear {P : Type*} [AddCommGroup P] [Module ℝ P] (A : Set P) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

/-- The predicate (on `n`) that there exist `n` points in `ℝ²`, no three on a line and no four on
a circle, such that all pairwise distances are integers (formal-conjectures definition). -/
def Erdos213For (n : ℕ) : Prop := ∃ S : Set (EuclideanSpace ℝ (Fin 2)), S.Finite ∧ S.ncard = n ∧
    NonTrilinear S ∧
    (∀ Q : Set (EuclideanSpace ℝ (Fin 2)), Q ⊆ S ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q) ∧
    (S.Pairwise fun p₁ p₂ => dist p₁ p₂ ∈ Set.range Int.cast)

/-- The seven Kreisel–Kurz points `(xᵢ, yᵢ √2002)` (arXiv:0804.1303, Fig. 1). -/
noncomputable def kk : Fin 7 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0],
    !₂[22270, 0],
    !₂[26127018 / 2227, 932064 / 2227 * Real.sqrt 2002],
    !₂[245363 / 17, 3144 / 17 * Real.sqrt 2002],
    !₂[17615968 / 2227, 238464 / 2227 * Real.sqrt 2002],
    !₂[56068 / 17, 3144 / 17 * Real.sqrt 2002],
    !₂[19079044 / 2227, -54168 / 2227 * Real.sqrt 2002]]

/-- The integer distances `dist (kk i) (kk j)` for `i < j` (row `i`, entry `j`). -/
def kkDist : Fin 7 → Fin 7 → ℤ :=
  ![![0, 22270, 22098, 16637, 9248, 8908, 8636],
    ![22270, 0, 21488, 11397, 15138, 20698, 13746],
    ![22098, 21488, 0, 10795, 14450, 13430, 20066],
    ![16637, 11397, 10795, 0, 7395, 11135, 11049],
    ![9248, 15138, 14450, 7395, 0, 5780, 5916],
    ![8908, 20698, 13430, 11135, 5780, 0, 10744],
    ![8636, 13746, 20066, 11049, 5916, 10744, 0]]


/-! ### Certificate data and helper lemmas

All seven coordinates have denominator dividing `2227 = 17 * 131`, so we clear denominators
once and record the integer coordinates `kkXI i = 2227 * xᵢ`, `kkYI i = 2227 * yᵢ` (with `yᵢ`
in units of `√2002`).  Every arithmetic fact about the configuration then becomes either a
*symbolic* polynomial identity in `√2002` (closed by `linear_combination` with
`√2002 ^ 2 = 2002`) or a finite integer computation over `Fin 7` tuples (closed by `decide`).
-/

theorem kk_sq_sqrt : Real.sqrt 2002 ^ 2 = 2002 := Real.sq_sqrt (by norm_num)

theorem kk_sqrt_pos : 0 < Real.sqrt 2002 := Real.sqrt_pos.mpr (by norm_num)

/-- `2227 * xᵢ`, the cleared-denominator first coordinates of the seven points. -/
def kkXI : Fin 7 → ℤ := ![0, 49595290, 26127018, 32142553, 17615968, 7344908, 19079044]

/-- `2227 * yᵢ`, the cleared-denominator second coordinates in units of `√2002`. -/
def kkYI : Fin 7 → ℤ := ![0, 0, 932064, 411864, 238464, 411864, -54168]

theorem kk_apply_zero (i : Fin 7) : kk i 0 = (kkXI i : ℝ) / 2227 := by
  fin_cases i <;> simp [kk, kkXI] <;> norm_num

theorem kk_apply_one (i : Fin 7) : kk i 1 = (kkYI i : ℝ) / 2227 * Real.sqrt 2002 := by
  fin_cases i <;> simp [kk, kkYI] <;> norm_num

theorem dist_sq_eq (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem dist_eq_of_sq {p q : EuclideanSpace ℝ (Fin 2)} {d : ℝ} (hd : 0 ≤ d)
    (h : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = d ^ 2) : dist p q = d := by
  have h2 : dist p q ^ 2 = d ^ 2 := by rw [dist_sq_eq]; exact h
  calc dist p q = Real.sqrt (dist p q ^ 2) := (Real.sqrt_sq dist_nonneg).symm
    _ = Real.sqrt (d ^ 2) := by rw [h2]
    _ = d := Real.sqrt_sq hd

/-- The collinearity determinant of three of the points, scaled by `2227 ^ 2 / √2002`. -/
def kkd3 (i j k : Fin 7) : ℤ :=
  (kkXI j - kkXI i) * (kkYI k - kkYI i) - (kkYI j - kkYI i) * (kkXI k - kkXI i)

theorem kk_det3_val (i j k : Fin 7) :
    (kk j 0 - kk i 0) * (kk k 1 - kk i 1) - (kk j 1 - kk i 1) * (kk k 0 - kk i 0)
      = (kkd3 i j k : ℝ) / 2227 ^ 2 * Real.sqrt 2002 := by
  simp only [kk_apply_zero, kk_apply_one]
  push_cast [kkd3]
  ring

set_option maxRecDepth 100000 in
theorem kkd3_ne_zero : ∀ i j k : Fin 7, i ≠ j → j ≠ k → i ≠ k → kkd3 i j k ≠ 0 := by decide

/-- Three collinear points in the plane have vanishing determinant. -/
theorem collinear_det {a b c : EuclideanSpace ℝ (Fin 2)}
    (h : Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  rw [collinear_iff_of_mem (Set.mem_insert a _)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨t, ht⟩ := hv c (by simp)
  subst hr
  subst ht
  simp [PiLp.add_apply, PiLp.smul_apply]
  ring

/-- The concyclicity determinant `det ![![x² + y², x, y, 1], …]` of four planar points.  It
vanishes exactly when the four points are concyclic or collinear. -/
noncomputable def kkDet4 (x0 y0 x1 y1 x2 y2 x3 y3 : ℝ) : ℝ :=
  (x0 ^ 2 + y0 ^ 2) * (x1 * (y2 - y3) - y1 * (x2 - x3) + (x2 * y3 - y2 * x3))
    - (x1 ^ 2 + y1 ^ 2) * (x0 * (y2 - y3) - y0 * (x2 - x3) + (x2 * y3 - y2 * x3))
    + (x2 ^ 2 + y2 ^ 2) * (x0 * (y1 - y3) - y0 * (x1 - x3) + (x1 * y3 - y1 * x3))
    - (x3 ^ 2 + y3 ^ 2) * (x0 * (y1 - y2) - y0 * (x1 - x2) + (x1 * y2 - y1 * x2))

/-- Four concyclic points have vanishing concyclicity determinant: the vector
`(1, -2u, -2v, u² + v² - r²)` built from the centre `(u, v)` and radius `r` lies in the
kernel of the matrix, and expanding along the first column gives the identity below. -/
theorem cospherical_det4 {p0 p1 p2 p3 : EuclideanSpace ℝ (Fin 2)}
    (h : EuclideanGeometry.Cospherical ({p0, p1, p2, p3} : Set (EuclideanSpace ℝ (Fin 2)))) :
    kkDet4 (p0 0) (p0 1) (p1 0) (p1 1) (p2 0) (p2 1) (p3 0) (p3 1) = 0 := by
  obtain ⟨c, r, hc⟩ := h
  have e0 : (p0 0 - c 0) ^ 2 + (p0 1 - c 1) ^ 2 = r ^ 2 := by
    rw [← dist_sq_eq, hc p0 (by simp)]
  have e1 : (p1 0 - c 0) ^ 2 + (p1 1 - c 1) ^ 2 = r ^ 2 := by
    rw [← dist_sq_eq, hc p1 (by simp)]
  have e2 : (p2 0 - c 0) ^ 2 + (p2 1 - c 1) ^ 2 = r ^ 2 := by
    rw [← dist_sq_eq, hc p2 (by simp)]
  have e3 : (p3 0 - c 0) ^ 2 + (p3 1 - c 1) ^ 2 = r ^ 2 := by
    rw [← dist_sq_eq, hc p3 (by simp)]
  simp only [kkDet4]
  linear_combination
    (p1 0 * (p2 1 - p3 1) - p1 1 * (p2 0 - p3 0) + (p2 0 * p3 1 - p2 1 * p3 0)) * e0
      - (p0 0 * (p2 1 - p3 1) - p0 1 * (p2 0 - p3 0) + (p2 0 * p3 1 - p2 1 * p3 0)) * e1
      + (p0 0 * (p1 1 - p3 1) - p0 1 * (p1 0 - p3 0) + (p1 0 * p3 1 - p1 1 * p3 0)) * e2
      - (p0 0 * (p1 1 - p2 1) - p0 1 * (p1 0 - p2 0) + (p1 0 * p2 1 - p1 1 * p2 0)) * e3

/-- Substituting `(Xᵢ / 2227, Yᵢ / 2227 * s)` with `s ^ 2 = 2002` into `kkDet4`:  every term of
the expansion is linear in the `y`-column, so the determinant is `s` times a rational number. -/
theorem kkDet4_subst (X0 Y0 X1 Y1 X2 Y2 X3 Y3 s : ℝ) (hs : s ^ 2 = 2002) :
    kkDet4 (X0 / 2227) (Y0 / 2227 * s) (X1 / 2227) (Y1 / 2227 * s) (X2 / 2227) (Y2 / 2227 * s)
        (X3 / 2227) (Y3 / 2227 * s)
      = ((X0 ^ 2 + 2002 * Y0 ^ 2) * (X1 * (Y2 - Y3) - Y1 * (X2 - X3) + (X2 * Y3 - Y2 * X3))
          - (X1 ^ 2 + 2002 * Y1 ^ 2) * (X0 * (Y2 - Y3) - Y0 * (X2 - X3) + (X2 * Y3 - Y2 * X3))
          + (X2 ^ 2 + 2002 * Y2 ^ 2) * (X0 * (Y1 - Y3) - Y0 * (X1 - X3) + (X1 * Y3 - Y1 * X3))
          - (X3 ^ 2 + 2002 * Y3 ^ 2) * (X0 * (Y1 - Y2) - Y0 * (X1 - X2) + (X1 * Y2 - Y1 * X2)))
        / 2227 ^ 4 * s := by
  simp only [kkDet4]
  linear_combination
    (s * (Y0 ^ 2 * (X1 * (Y2 - Y3) - Y1 * (X2 - X3) + (X2 * Y3 - Y2 * X3))
          - Y1 ^ 2 * (X0 * (Y2 - Y3) - Y0 * (X2 - X3) + (X2 * Y3 - Y2 * X3))
          + Y2 ^ 2 * (X0 * (Y1 - Y3) - Y0 * (X1 - X3) + (X1 * Y3 - Y1 * X3))
          - Y3 ^ 2 * (X0 * (Y1 - Y2) - Y0 * (X1 - X2) + (X1 * Y2 - Y1 * X2))) / 2227 ^ 4) * hs

/-- `2227 ^ 2 * (xᵢ ^ 2 + 2002 * yᵢ ^ 2)`, the squared norm of the `i`-th point. -/
def kkNI (i : Fin 7) : ℤ := kkXI i ^ 2 + 2002 * kkYI i ^ 2

/-- The `3 × 3` minor `det ![![x, y, 1], …]`, scaled by `2227 ^ 2 / √2002`. -/
def kkm3 (a b c : Fin 7) : ℤ :=
  kkXI a * (kkYI b - kkYI c) - kkYI a * (kkXI b - kkXI c) + (kkXI b * kkYI c - kkYI b * kkXI c)

/-- The concyclicity determinant of four of the points, scaled by `2227 ^ 4 / √2002`. -/
def kkq4 (a b c d : Fin 7) : ℤ :=
  kkNI a * kkm3 b c d - kkNI b * kkm3 a c d + kkNI c * kkm3 a b d - kkNI d * kkm3 a b c

theorem kk_det4_val (a b c d : Fin 7) :
    kkDet4 (kk a 0) (kk a 1) (kk b 0) (kk b 1) (kk c 0) (kk c 1) (kk d 0) (kk d 1)
      = (kkq4 a b c d : ℝ) / 2227 ^ 4 * Real.sqrt 2002 := by
  simp only [kk_apply_zero, kk_apply_one]
  rw [kkDet4_subst _ _ _ _ _ _ _ _ _ kk_sq_sqrt]
  push_cast [kkq4, kkNI, kkm3]
  ring

set_option maxRecDepth 4000000 in
theorem kkq4_ne_zero : ∀ a b c d : Fin 7, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    kkq4 a b c d ≠ 0 := by decide

theorem kk_dist (i j : Fin 7) : dist (kk i) (kk j) = kkDist i j := by
  have hkey : ∀ a b : Fin 7,
      (kkXI a - kkXI b) ^ 2 + 2002 * (kkYI a - kkYI b) ^ 2 = (2227 * kkDist a b) ^ 2 := by decide
  have hnn : ∀ a b : Fin 7, 0 ≤ kkDist a b := by decide
  have h : ((kkXI i : ℝ) - (kkXI j : ℝ)) ^ 2 + 2002 * ((kkYI i : ℝ) - (kkYI j : ℝ)) ^ 2
      = (2227 * (kkDist i j : ℝ)) ^ 2 := by exact_mod_cast hkey i j
  refine dist_eq_of_sq (by exact_mod_cast hnn i j) ?_
  simp only [kk_apply_zero, kk_apply_one]
  linear_combination (1 / 2227 ^ 2) * h
    + (((kkYI i : ℝ) - (kkYI j : ℝ)) ^ 2 / 2227 ^ 2) * kk_sq_sqrt

theorem kk_injective : Function.Injective kk := by
  have key : ∀ a b : Fin 7, kkDist a b = 0 → a = b := by decide
  intro i j hij
  refine key i j ?_
  have h : ((kkDist i j : ℤ) : ℝ) = 0 := by rw [← kk_dist, hij, dist_self]
  exact_mod_cast h

theorem kk_not_collinear (i j k : Fin 7) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Collinear ℝ ({kk i, kk j, kk k} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro h
  have hd := collinear_det h
  rw [kk_det3_val] at hd
  have hq : (kkd3 i j k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (kkd3_ne_zero i j k hij hjk hik)
  rcases mul_eq_zero.mp hd with h1 | h1
  · rcases div_eq_zero_iff.mp h1 with h2 | h2
    · exact hq h2
    · norm_num at h2
  · exact absurd h1 (ne_of_gt kk_sqrt_pos)

theorem kk_not_cospherical (i j k l : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ¬ EuclideanGeometry.Cospherical ({kk i, kk j, kk k, kk l} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro h
  have hd := cospherical_det4 h
  rw [kk_det4_val] at hd
  have hq : (kkq4 i j k l : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (kkq4_ne_zero i j k l hij hik hil hjk hjl hkl)
  rcases mul_eq_zero.mp hd with h1 | h1
  · rcases div_eq_zero_iff.mp h1 with h2 | h2
    · exact hq h2
    · norm_num at h2
  · exact absurd h1 (ne_of_gt kk_sqrt_pos)

/-- **Erdős #213, the Kreisel–Kurz construction (`n = 7`).**  Exactly the formal-conjectures
statement `Erdos213.erdos_213.variants.KK08`.  The question for `n ≥ 8` is open and not claimed. -/
theorem erdos_213_KK08 : Erdos213For 7 := by
  refine ⟨Set.range kk, Set.finite_range kk, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective kk_injective]
    simp
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ z ⟨k, rfl⟩ hxy hyz hxz
    exact kk_not_collinear i j k (fun h => hxy (by rw [h])) (fun h => hyz (by rw [h]))
      (fun h => hxz (by rw [h]))
  · rintro Q ⟨hQ, hcard⟩
    rw [Set.ncard_eq_four] at hcard
    obtain ⟨p, q, r, t, hpq, hpr, hpt, hqr, hqt, hrt, rfl⟩ := hcard
    obtain ⟨i, rfl⟩ := hQ (by simp : p ∈ ({p, q, r, t} : Set (EuclideanSpace ℝ (Fin 2))))
    obtain ⟨j, rfl⟩ := hQ (by simp : q ∈ ({kk i, q, r, t} : Set (EuclideanSpace ℝ (Fin 2))))
    obtain ⟨k, rfl⟩ := hQ (by simp : r ∈ ({kk i, kk j, r, t} : Set (EuclideanSpace ℝ (Fin 2))))
    obtain ⟨l, rfl⟩ := hQ (by simp : t ∈ ({kk i, kk j, kk k, t} : Set (EuclideanSpace ℝ (Fin 2))))
    exact kk_not_cospherical i j k l (fun h => hpq (by rw [h])) (fun h => hpr (by rw [h]))
      (fun h => hpt (by rw [h])) (fun h => hqr (by rw [h])) (fun h => hqt (by rw [h]))
      (fun h => hrt (by rw [h]))
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ _
    exact ⟨kkDist i j, (kk_dist i j).symm⟩
