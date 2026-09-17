/-
Comparator-style challenge module for JSP-000117 / Erdős Problem #104 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos104Challenge

open Classical in
/-- The unit circle centred at `c` contains at least three points of `P`. -/
def IsRichCenter (P : Finset (EuclideanSpace ℝ (Fin 2))) (c : EuclideanSpace ℝ (Fin 2)) : Prop :=
  3 ≤ (P.filter (fun p => dist p c = 1)).card

/-- The number of unit circles containing at least three points of `P`. -/
noncomputable def unitCircleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {c : EuclideanSpace ℝ (Fin 2) | IsRichCenter P c}

theorem not_exists_unitCircleCount_gt (n : ℕ) :
    ¬ ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧ n * (n - 1) < 3 * unitCircleCount P := by
  sorry

theorem three_mul_unitCircleCount_le (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    3 * unitCircleCount P ≤ P.card * (P.card - 1) := by
  sorry

theorem richCenters_finite (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    {c : EuclideanSpace ℝ (Fin 2) | IsRichCenter P c}.Finite := by
  sorry

theorem exists_two_centers (p q : EuclideanSpace ℝ (Fin 2)) (hpq : p ≠ q) :
    ∃ c₁ c₂ : EuclideanSpace ℝ (Fin 2), ∀ c : EuclideanSpace ℝ (Fin 2),
      dist p c = 1 → dist q c = 1 → c = c₁ ∨ c = c₂ := by
  sorry

theorem three_mul_card_le_of_rich (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : ∀ c ∈ S, IsRichCenter P c) :
    3 * S.card ≤ P.card * (P.card - 1) := by
  sorry

end Erdos104Challenge
