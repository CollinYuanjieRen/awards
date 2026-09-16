import Erdos503IsoscelesSix

#print axioms erdos_503_R2_six_point_isosceles_set
#print axioms six_mem_isosceles_ncards
#print axioms exists_six_points_no_three_distinct_distances

/-- Erdős #503 (`d = 2`), construction half: a six-point planar set with every triangle isosceles. -/
example : ∃ A : Set (EuclideanSpace ℝ (Fin 2)), A.IsIsosceles ∧ A.ncard = 6 :=
  erdos_503_R2_six_point_isosceles_set

-- The unused binder `hA` is part of the formal-conjectures set-builder syntax; the lint is silenced.
set_option linter.unusedVariables false in
/-- The formal-conjectures set membership used by `erdos_503.variants.R2`. -/
example : 6 ∈ {(A.ncard) | (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : A.IsIsosceles)} :=
  six_mem_isosceles_ncards

/-- The predicates unfold to the formal-conjectures definitions. -/
example {α : Type} [Dist α] (A : Set α) :
    A.IsIsosceles ↔ Nonempty A ∧ A.Triplewise (IsIsosceles · · ·) := Iff.rfl
