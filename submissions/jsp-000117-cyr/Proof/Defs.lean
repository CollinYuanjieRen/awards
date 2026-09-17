import Mathlib

/-!
# Unit circles through three points: definitions and the two-circles lemma

This module fixes the frozen definitions used by the scoped component of Erdős problem #104
(the elementary double-counting upper bound on the number of unit circles containing at least
three of `n` given points in the plane) and proves the geometric input to that bound:
a pair of distinct points lies on at most two unit circles.

Points are Mathlib's `EuclideanSpace ℝ (Fin 2)`.  A unit circle is identified with its centre
`c`, and "the circle centred at `c` contains `p`" is `dist p c = 1`.
-/

namespace Erdos104

open Classical in
/-- `IsRichCenter P c` says that the unit circle centred at `c` contains at least three points
of the finite point set `P`. -/
def IsRichCenter (P : Finset (EuclideanSpace ℝ (Fin 2))) (c : EuclideanSpace ℝ (Fin 2)) : Prop :=
  3 ≤ (P.filter (fun p => dist p c = 1)).card

/-- `unitCircleCount P` is the number of distinct unit circles containing at least three points
of `P`, counted through their centres.  It is honest (not a junk value) because the set of such
centres is finite; see `Erdos104.richCenters_finite`. -/
noncomputable def unitCircleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {c : EuclideanSpace ℝ (Fin 2) | IsRichCenter P c}

/-- (T4) Two distinct points lie on at most two unit circles: there are two centres `c₁`, `c₂`
such that every centre `c` at distance `1` from both `p` and `q` is one of them.

Proof: such a `c` lies on the unit circles centred at `p` and at `q`, and two distinct circles
in the plane meet in at most two points
(`EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`). -/
theorem exists_two_centers (p q : EuclideanSpace ℝ (Fin 2)) (hpq : p ≠ q) :
    ∃ c₁ c₂ : EuclideanSpace ℝ (Fin 2), ∀ c : EuclideanSpace ℝ (Fin 2),
      dist p c = 1 → dist q c = 1 → c = c₁ ∨ c = c₂ := by
  classical
  by_cases h : ∃ c₁ c₂ : EuclideanSpace ℝ (Fin 2), c₁ ≠ c₂ ∧
      (dist p c₁ = 1 ∧ dist q c₁ = 1) ∧ (dist p c₂ = 1 ∧ dist q c₂ = 1)
  · -- Two distinct common centres already exist; they are the witnesses.
    obtain ⟨c₁, c₂, hne, ⟨h₁p, h₁q⟩, h₂p, h₂q⟩ := h
    refine ⟨c₁, c₂, fun c hcp hcq => ?_⟩
    exact EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (finrank_euclideanSpace_fin) (r₁ := 1) (r₂ := 1) hpq hne
      (by rw [dist_comm]; exact h₁p) (by rw [dist_comm]; exact h₂p)
      (by rw [dist_comm]; exact hcp)
      (by rw [dist_comm]; exact h₁q) (by rw [dist_comm]; exact h₂q)
      (by rw [dist_comm]; exact hcq)
  · -- Otherwise all common centres coincide, so a single witness (used twice) suffices.
    by_cases hex : ∃ c : EuclideanSpace ℝ (Fin 2), dist p c = 1 ∧ dist q c = 1
    · obtain ⟨c₀, hc₀p, hc₀q⟩ := hex
      refine ⟨c₀, c₀, fun c hcp hcq => Or.inl ?_⟩
      by_contra hcc
      exact h ⟨c, c₀, hcc, ⟨hcp, hcq⟩, hc₀p, hc₀q⟩
    · exact ⟨p, p, fun c hcp hcq => absurd ⟨c, hcp, hcq⟩ hex⟩

end Erdos104
