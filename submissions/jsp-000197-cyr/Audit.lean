import Erdos213Heptagon

#print axioms erdos_213_KK08
#print axioms kk_dist
#print axioms kk_not_collinear
#print axioms kk_not_cospherical

/-- Erdős #213, the Kreisel–Kurz construction, in the formal-conjectures shape
`Erdos213.erdos_213.variants.KK08 : Erdos213For 7`. -/
example : Erdos213For 7 := erdos_213_KK08

/-- The predicate unfolds to the formal-conjectures definition. -/
example (n : ℕ) : Erdos213For n ↔ ∃ S : Set (EuclideanSpace ℝ (Fin 2)), S.Finite ∧ S.ncard = n ∧
    NonTrilinear S ∧
    (∀ Q : Set (EuclideanSpace ℝ (Fin 2)), Q ⊆ S ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q) ∧
    (S.Pairwise fun p₁ p₂ => dist p₁ p₂ ∈ Set.range Int.cast) := Iff.rfl
