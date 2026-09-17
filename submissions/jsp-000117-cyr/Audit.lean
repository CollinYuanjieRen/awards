import Proof

open Erdos104

#print axioms Erdos104.not_exists_unitCircleCount_gt
#print axioms Erdos104.three_mul_unitCircleCount_le
#print axioms Erdos104.richCenters_finite
#print axioms Erdos104.exists_two_centers
#print axioms Erdos104.three_mul_card_le_of_rich

example : ∀ n : ℕ, ¬ ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧
    n * (n - 1) < 3 * unitCircleCount P := Erdos104.not_exists_unitCircleCount_gt
example : ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), 3 * unitCircleCount P ≤ P.card * (P.card - 1) :=
  Erdos104.three_mul_unitCircleCount_le
example : ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), {c : EuclideanSpace ℝ (Fin 2) | IsRichCenter P c}.Finite :=
  Erdos104.richCenters_finite
example : ∀ p q : EuclideanSpace ℝ (Fin 2), p ≠ q → ∃ c₁ c₂ : EuclideanSpace ℝ (Fin 2),
    ∀ c : EuclideanSpace ℝ (Fin 2), dist p c = 1 → dist q c = 1 → c = c₁ ∨ c = c₂ :=
  Erdos104.exists_two_centers
example : ∀ (P S : Finset (EuclideanSpace ℝ (Fin 2))), (∀ c ∈ S, IsRichCenter P c) →
    3 * S.card ≤ P.card * (P.card - 1) := Erdos104.three_mul_card_le_of_rich

#print Erdos104.IsRichCenter
#print Erdos104.unitCircleCount
