import MerLeanExperiment.CapSemantics
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-! The exact three-point face of the ordinary planar minimax-angle problem. -/

namespace PlanarMinimax

/-- Vertices of a side-length-two equilateral triangle. -/
noncomputable def equilateralPoints : Fin 3 → Plane :=
  ![!₂[0, 0], !₂[2, 0], !₂[1, Real.sqrt 3]]

/-- The explicit equilateral vertices are indexed injectively. -/
theorem equilateralPoints_injective : Function.Injective equilateralPoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [equilateralPoints] at hij ⊢

/-- Distinct explicit equilateral vertices have distance two. -/
theorem equilateralPoints_dist {i j : Fin 3} (hij : i ≠ j) :
    dist (equilateralPoints i) (equilateralPoints j) = 2 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals
    apply (sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mp
    norm_num [equilateralPoints, EuclideanSpace.dist_sq_eq, Real.dist_eq, hsqrt]

/-- Equal side lengths force the corresponding triangle angle to be `π / 3`. -/
theorem angle_eq_pi_div_three_of_equal_sides {A B C : Plane}
    (hA : dist A B = dist A C) (hB : dist B A = dist B C) (hne : B ≠ A) :
    EuclideanGeometry.angle A B C = Real.pi / 3 := by
  have hβγ : EuclideanGeometry.angle A B C = EuclideanGeometry.angle B C A :=
    (EuclideanGeometry.angle_eq_angle_of_dist_eq hA).trans
      (EuclideanGeometry.angle_comm A C B)
  have hαγ : EuclideanGeometry.angle C A B = EuclideanGeometry.angle B C A :=
    (EuclideanGeometry.angle_comm C A B).trans
      (EuclideanGeometry.angle_eq_angle_of_dist_eq hB)
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi C hne
  linarith

/-- The explicit equilateral triangle realizes the cap `π / 3`. -/
theorem realizableCap_three : RealizableCap 3 (Real.pi / 3) := by
  refine ⟨equilateralPoints, equilateralPoints_injective, ?_⟩
  intro i j k hij hjk hik
  have hA : dist (equilateralPoints i) (equilateralPoints j) =
      dist (equilateralPoints i) (equilateralPoints k) := by
    rw [equilateralPoints_dist hij, equilateralPoints_dist hik]
  have hB : dist (equilateralPoints j) (equilateralPoints i) =
      dist (equilateralPoints j) (equilateralPoints k) := by
    rw [equilateralPoints_dist hij.symm, equilateralPoints_dist hjk]
  exact (angle_eq_pi_div_three_of_equal_sides hA hB
    (equilateralPoints_injective.ne hij.symm)).le

/-- Every realizable three-point cap is at least `π / 3`. -/
theorem three_cap_lower {bound : ℝ} (hbound : RealizableCap 3 bound) :
    Real.pi / 3 ≤ bound := by
  rcases hbound with ⟨points, hinjective, hcap⟩
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (points 2)
    (hinjective.ne (by omega : (1 : Fin 3) ≠ 0))
  have h₀ := hcap 0 1 2 (by omega) (by omega) (by omega)
  have h₁ := hcap 1 2 0 (by omega) (by omega) (by omega)
  have h₂ := hcap 2 0 1 (by omega) (by omega) (by omega)
  linarith

/-- The ordinary three-point minimax angle is exactly `π / 3`. -/
theorem minimaxAngle_three : minimaxAngle 3 = Real.pi / 3 := by
  apply le_antisymm
  · unfold minimaxAngle
    exact csInf_le (realizableCap_bddBelow (by norm_num)) realizableCap_three
  · unfold minimaxAngle
    exact le_csInf ⟨Real.pi / 3, realizableCap_three⟩ fun _ hbound ↦
      three_cap_lower hbound

#print axioms minimaxAngle_three

end PlanarMinimax
