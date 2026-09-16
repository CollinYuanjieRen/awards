import EmptyPentagon

open Horton

#print axioms Horton.forces_empty_triangle_iff
#print axioms Horton.forces_empty_quadrilateral_iff
#print axioms Horton.forces_empty_pentagon_iff
#print axioms Horton.forcesEmptyKGon_five_ten
#print axioms Horton.not_forcesEmptyKGon_five_nine
#print axioms Horton.forcesEmptyKGon_four_five
#print axioms Horton.not_forcesEmptyKGon_four_four
#print axioms Horton.exists_convex_pentagon
#print axioms Horton.exists_convex_pentagon_few_interior
#print axioms Horton.exists_empty_pentagon_of_few_interior

/-- `h(3) = 3`: exactly the sets of at least three points force an empty triangle. -/
example (n : ℕ) : ForcesEmptyKGon 3 n ↔ 3 ≤ n := forces_empty_triangle_iff n

/-- `h(4) = 5`: exactly the sets of at least five points force an empty convex quadrilateral. -/
example (n : ℕ) : ForcesEmptyKGon 4 n ↔ 5 ≤ n := forces_empty_quadrilateral_iff n

/-- `h(5) = 10`: exactly the sets of at least ten points force an empty convex pentagon. -/
example (n : ℕ) : ForcesEmptyKGon 5 n ↔ 10 ≤ n := forces_empty_pentagon_iff n

/-- The unfolded form of the pentagon threshold, with no auxiliary predicate on the left. -/
example (n : ℕ) :
    (∀ S : Finset (ℝ × ℝ), S.card = n →
        (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → orient a b c ≠ 0) →
        ∃ V : Finset (ℝ × ℝ), V.card = 5 ∧ V ⊆ S ∧
          ConvexIndependent ℝ (fun v : (V : Set (ℝ × ℝ)) => (v : ℝ × ℝ)) ∧
          ∀ p ∈ S, p ∉ V → p ∉ interior (convexHull ℝ (V : Set (ℝ × ℝ)))) ↔ 10 ≤ n :=
  forces_empty_pentagon_iff n
