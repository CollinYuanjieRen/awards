import Erdos132FourPoints

open scoped Finset

#print axioms erdos_132_four_points

/-- Erdős #132: the n = 4 counterexample (two glued equilateral triangles). -/
example : ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), #A = 4 ∧
    #{d ∈ distanceSet A | distanceMultiplicity A d ≤ 4} < 2 := erdos_132_four_points

/-- The definitions are the formal-conjectures ones. -/
example {X : Type*} [MetricSpace X] (points : Finset X) :
    distanceSet points = points.offDiag.image (fun (pair : X × X) => dist pair.1 pair.2) := rfl
example {X : Type*} [MetricSpace X] (points : Finset X) (d : ℝ) :
    distanceMultiplicity points d =
      #(points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d) / 2 := rfl
