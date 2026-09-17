import Erdos193Walk.Collinear

/-!
# Erdős Problem 193

The statement below (`IsSWalk`, `HasCollinearTriple`, and the shape of `erdos_193`) is copied from
`FormalConjectures/ErdosProblems/193.lean` of google-deepmind/formal-conjectures (pinned in
`ref/fc193-official.lean`), with the `answer` placeholder replaced by the answer `False`: there is an
infinite walk with steps from a finite set and no three collinear points (Cambie–Kalviainen 2026).
-/

open Set

namespace Erdos193

/-- An $S$-walk is a sequence where every difference is in $S$. -/
def IsSWalk {V : Type*} [AddCommGroup V] (S : Set V) (a : ℕ → V) : Prop :=
  ∀ n, a (n + 1) - a n ∈ S

/-- True if set $A$ contains 3 distinct collinear points over $R$. -/
def HasCollinearTriple (R) {V : Type*} [DivisionRing R] [AddCommGroup V] [Module R V] (A : Set V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Collinear R ({x, y, z} : Set V)

/-- The positive form: a finite step set and an infinite walk with no collinear triple. -/
theorem exists_walk_no_collinear_triple :
    ∃ S : Set (Fin 3 → ℤ), S.Finite ∧ ∃ a : ℕ → Fin 3 → ℤ, IsSWalk S a ∧ (range a).Infinite ∧
      ¬ HasCollinearTriple ℚ (range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ)) := by
  refine ⟨Erdos193Walk.stepSet, Erdos193Walk.stepSet_finite, Erdos193Walk.P, ?_, ?_, ?_⟩
  · intro n
    exact Erdos193Walk.P_succ_sub_mem n
  · exact Set.infinite_range_of_injective Erdos193Walk.P_injective
  · exact Erdos193Walk.no_collinear_triple

/-- Erdős Problem 193, stated as in formal-conjectures with the answer `False`. -/
theorem erdos_193 :
    False ↔ ∀ S : Set (Fin 3 → ℤ), S.Finite →
      ∀ a : ℕ → Fin 3 → ℤ, IsSWalk S a → (range a).Infinite →
      HasCollinearTriple ℚ (range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ)) := by
  refine iff_of_false not_false ?_
  intro hall
  obtain ⟨S, hS, a, hwalk, hinf, hno⟩ := exists_walk_no_collinear_triple
  exact hno (hall S hS a hwalk hinf)

end Erdos193
