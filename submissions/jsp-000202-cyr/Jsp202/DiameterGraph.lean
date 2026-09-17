import Mathlib

open Finset
open scoped Classical

namespace HopfPannwitz

variable {n : ℕ}

/-- The "diameter graph" of a finite point configuration `P : Fin n → ℝ²`: two indices are
adjacent when they are distinct and their points are at distance exactly `D`. -/
def diameterGraph (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ dist (P i) (P j) = D
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

noncomputable instance (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ) :
    DecidableRel (diameterGraph P D).Adj := Classical.decRel _

/-- Handshake corollary: if every vertex of the diameter graph has degree at most `2`,
then it has at most `n` edges. -/
theorem card_edges_le_of_degree_le_two (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ)
    (h : ∀ i, (diameterGraph P D).degree i ≤ 2) :
    (diameterGraph P D).edgeFinset.card ≤ n := by
  have key : 2 * (diameterGraph P D).edgeFinset.card ≤ 2 * n := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
    calc ∑ v, (diameterGraph P D).degree v ≤ ∑ _v : Fin n, 2 :=
          Finset.sum_le_sum (fun i _ => h i)
      _ = 2 * n := by simp [mul_comm]
  omega

end HopfPannwitz
