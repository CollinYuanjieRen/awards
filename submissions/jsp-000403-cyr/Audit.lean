import Erdos503IsoscelesLower

#print axioms erdos_503_lower_bound_explicit
#print axioms awConfig_isIsosceles
#print axioms exists_isometry_awConfig

/-- Alweiss–Weisenberg: an isosceles set of `C(d+1, 2) + 1` points in `ℝ^d`, for every `d`. -/
example (d : ℕ) : ∃ A : Set (EuclideanSpace ℝ (Fin d)), A.IsIsosceles ∧ A.ncard = (d + 1).choose 2 + 1 :=
  erdos_503_lower_bound_explicit d

/-- The predicate unfolds to the formal-conjectures definition. -/
example {α : Type} [Dist α] (A : Set α) :
    A.IsIsosceles ↔ Nonempty A ∧ A.Triplewise (IsIsosceles · · ·) := Iff.rfl
