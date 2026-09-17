import Mathlib

/-!
# Erdős Problem #132: the `n = 4` counterexample (two glued equilateral triangles)

Erdős and Pach asked: for a set `A` of `n` points in the plane, must there be two distances which
occur at least once but between at most `n` pairs of points, and must the number of such
distances tend to infinity (OPEN; not addressed here)?  The problem page records: "Erdős
believed that for `n ≥ 5` there must always exist at least two such distances.  This is false
for `n = 4`, as witnessed by two equilateral triangles of the same side-length glued together."

This file proves that `n = 4` statement, with the formal-conjectures definitions `distanceSet`
and `distanceMultiplicity` (`FormalConjecturesForMathlib/Geometry/Metric.lean`) copied
verbatim: there is a set of four points in `ℝ²` with fewer than two distances of multiplicity
at most `4`.  The witness is the rhombus `(0,0), (1,0), (1/2, √3/2), (1/2, −√3/2)`: the
distance `1` occurs between five pairs and the distance `√3` between one pair, so `√3` is the
only distance of multiplicity `≤ 4`.  Nothing about `n ≥ 5` or the growth question is claimed.
-/

open scoped Finset

variable {X : Type*} [MetricSpace X]

/-- Given a finite set of points in a metric space, we define the set of distances determined by
these points. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/-- Given a finite set of points in a metric space, we define the number of times a distance `d`
occurs between distinct points (unordered pairs). -/
noncomputable def distanceMultiplicity (points : Finset X) (d : ℝ) : ℕ :=
  #(points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d) / 2

/-- Distance between two explicitly given points of the Euclidean plane. -/
lemma erdos132_dist_pt (a b c d : ℝ) :
    dist (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) !₂[c, d]
      = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma erdos132_dist_one (a b c d : ℝ) (h : (a - c) ^ 2 + (b - d) ^ 2 = 1) :
    dist (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) !₂[c, d] = 1 := by
  rw [erdos132_dist_pt, h, Real.sqrt_one]

private lemma erdos132_dist_sqrt3 (a b c d : ℝ) (h : (a - c) ^ 2 + (b - d) ^ 2 = 3) :
    dist (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) !₂[c, d] = Real.sqrt 3 := by
  rw [erdos132_dist_pt, h]

/-- The four vertices of the rhombus formed by two glued unit equilateral triangles. -/
private noncomputable def P0 : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
private noncomputable def P1 : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
private noncomputable def P2 : EuclideanSpace ℝ (Fin 2) := !₂[1 / 2, Real.sqrt 3 / 2]
private noncomputable def P3 : EuclideanSpace ℝ (Fin 2) := !₂[1 / 2, -(Real.sqrt 3 / 2)]

private lemma P0_def : P0 = !₂[(0 : ℝ), 0] := rfl
private lemma P1_def : P1 = !₂[(1 : ℝ), 0] := rfl
private lemma P2_def : P2 = !₂[(1 / 2 : ℝ), Real.sqrt 3 / 2] := rfl
private lemma P3_def : P3 = !₂[(1 / 2 : ℝ), -(Real.sqrt 3 / 2)] := rfl

private lemma erdos132_sq_sqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma d01 : dist P0 P1 = 1 := by
  rw [P0_def, P1_def]; exact erdos132_dist_one _ _ _ _ (by norm_num)
private lemma d02 : dist P0 P2 = 1 := by
  rw [P0_def, P2_def]; exact erdos132_dist_one _ _ _ _ (by nlinarith [erdos132_sq_sqrt3])
private lemma d03 : dist P0 P3 = 1 := by
  rw [P0_def, P3_def]; exact erdos132_dist_one _ _ _ _ (by nlinarith [erdos132_sq_sqrt3])
private lemma d12 : dist P1 P2 = 1 := by
  rw [P1_def, P2_def]; exact erdos132_dist_one _ _ _ _ (by nlinarith [erdos132_sq_sqrt3])
private lemma d13 : dist P1 P3 = 1 := by
  rw [P1_def, P3_def]; exact erdos132_dist_one _ _ _ _ (by nlinarith [erdos132_sq_sqrt3])
private lemma d23 : dist P2 P3 = Real.sqrt 3 := by
  rw [P2_def, P3_def]; exact erdos132_dist_sqrt3 _ _ _ _ (by nlinarith [erdos132_sq_sqrt3])

private lemma d10 : dist P1 P0 = 1 := by rw [dist_comm]; exact d01
private lemma d20 : dist P2 P0 = 1 := by rw [dist_comm]; exact d02
private lemma d30 : dist P3 P0 = 1 := by rw [dist_comm]; exact d03
private lemma d21 : dist P2 P1 = 1 := by rw [dist_comm]; exact d12
private lemma d31 : dist P3 P1 = 1 := by rw [dist_comm]; exact d13
private lemma d32 : dist P3 P2 = Real.sqrt 3 := by rw [dist_comm]; exact d23

private lemma erdos132_ne_of_dist_one {p q : EuclideanSpace ℝ (Fin 2)} (h : dist p q = 1) :
    p ≠ q := by
  rintro rfl; rw [dist_self] at h; norm_num at h

private lemma h01 : P0 ≠ P1 := erdos132_ne_of_dist_one d01
private lemma h02 : P0 ≠ P2 := erdos132_ne_of_dist_one d02
private lemma h03 : P0 ≠ P3 := erdos132_ne_of_dist_one d03
private lemma h12 : P1 ≠ P2 := erdos132_ne_of_dist_one d12
private lemma h13 : P1 ≠ P3 := erdos132_ne_of_dist_one d13
private lemma h23 : P2 ≠ P3 := by
  rintro h
  have hd : dist P2 P3 = Real.sqrt 3 := d23
  rw [h, dist_self] at hd
  have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- The witness: two unit equilateral triangles glued along a common edge. -/
private noncomputable def rhombus : Finset (EuclideanSpace ℝ (Fin 2)) := {P0, P1, P2, P3}

private lemma rhombus_def : rhombus = {P0, P1, P2, P3} := rfl

private lemma rhombus_card : #rhombus = 4 := by
  rw [rhombus_def, Finset.card_insert_of_notMem (by simp [h01, h02, h03]),
    Finset.card_insert_of_notMem (by simp [h12, h13]),
    Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]

private lemma mem_rhombus {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ rhombus) :
    p = P0 ∨ p = P1 ∨ p = P2 ∨ p = P3 := by
  simpa [rhombus_def] using hp

private lemma erdos132_dist_cases {p q : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ rhombus)
    (hq : q ∈ rhombus) (hpq : p ≠ q) : dist p q = 1 ∨ dist p q = Real.sqrt 3 := by
  rcases mem_rhombus hp with rfl | rfl | rfl | rfl <;>
    rcases mem_rhombus hq with rfl | rfl | rfl | rfl <;>
      simp_all [d01, d02, d03, d12, d13, d23, d10, d20, d30, d21, d31, d32]

private lemma erdos132_distanceSet_mem {d : ℝ} (hd : d ∈ distanceSet rhombus) :
    d = 1 ∨ d = Real.sqrt 3 := by
  simp only [distanceSet, Finset.mem_image, Finset.mem_offDiag] at hd
  obtain ⟨⟨p, q⟩, ⟨hp, hq, hpq⟩, rfl⟩ := hd
  exact erdos132_dist_cases hp hq hpq

private lemma erdos132_not_one {pair : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hpair : pair ∈ rhombus.offDiag) (h : ¬ dist pair.1 pair.2 = 1) :
    pair = (P2, P3) ∨ pair = (P3, P2) := by
  obtain ⟨p, q⟩ := pair
  rw [Finset.mem_offDiag] at hpair
  obtain ⟨hp, hq, hpq⟩ := hpair
  simp only at hp hq hpq h
  rcases mem_rhombus hp with rfl | rfl | rfl | rfl <;>
    rcases mem_rhombus hq with rfl | rfl | rfl | rfl <;>
      simp_all [d01, d02, d03, d12, d13, d23, d10, d20, d30, d21, d31, d32, Prod.ext_iff]

private lemma erdos132_ten_le :
    10 ≤ #{pair ∈ rhombus.offDiag | dist pair.1 pair.2 = 1} := by
  have hcard : #rhombus.offDiag = 12 := by rw [Finset.offDiag_card, rhombus_card]
  have hsplit := Finset.card_filter_add_card_filter_not (s := rhombus.offDiag)
    (fun pair : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      dist pair.1 pair.2 = 1)
  have hle2 : #{pair ∈ rhombus.offDiag | ¬ dist pair.1 pair.2 = 1} ≤ 2 := by
    refine le_trans (Finset.card_le_card (t := ({(P2, P3), (P3, P2)} : Finset _)) ?_) ?_
    · intro pair hpair
      rw [Finset.mem_filter] at hpair
      rcases erdos132_not_one hpair.1 hpair.2 with h | h <;> simp [h]
    · exact le_trans (Finset.card_insert_le _ _) (by simp)
  omega

private lemma erdos132_mult_one : 5 ≤ distanceMultiplicity rhombus 1 := by
  rw [distanceMultiplicity]
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa using erdos132_ten_le)

/-- **Erdős #132, the `n = 4` counterexample**: some four points in the plane determine fewer than
two distances occurring between at most `4` pairs (two glued equilateral triangles: the side
length has multiplicity `5`, the long diagonal multiplicity `1`). -/
theorem erdos_132_four_points :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), #A = 4 ∧
      #{d ∈ distanceSet A | distanceMultiplicity A d ≤ 4} < 2 := by
  refine ⟨rhombus, rhombus_card, ?_⟩
  have hsub : {d ∈ distanceSet rhombus | distanceMultiplicity rhombus d ≤ 4}
      ⊆ ({Real.sqrt 3} : Finset ℝ) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rcases erdos132_distanceSet_mem hd.1 with rfl | rfl
    · exact absurd hd.2 (by have := erdos132_mult_one; omega)
    · simp
  have hle := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hle
  omega
