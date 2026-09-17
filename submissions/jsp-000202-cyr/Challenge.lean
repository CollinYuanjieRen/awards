import Mathlib

/-! Comparator-style challenge module (Mathlib-only definitions; targets with `sorry`, not imported by
the build) for JSP-000202 / Erdős #223: the planar Hopf–Pannwitz diameter theorem f₂(n) = n. -/

namespace Challenge223

/-- the "diameter graph": edges join the pairs at the extremal distance `D`. -/
def diameterGraph {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ dist (P i) (P j) = D
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

noncomputable instance {n} (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ) :
    DecidableRel (diameterGraph P D).Adj := Classical.decRel _

/-- the possible numbers of diameter pairs realizable by `n` planar points of diameter `D`. -/
def diameterPairCounts (n : ℕ) : Set ℕ :=
  {c | ∃ (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ),
      Function.Injective P ∧ (∀ i j, dist (P i) (P j) ≤ D) ∧
      (diameterGraph P D).edgeFinset.card = c}

/-- Hopf–Pannwitz (1934), planar case: the maximum number of diameter pairs among `n ≥ 3` points is `n`. -/
theorem hopf_pannwitz (n : ℕ) (hn : 3 ≤ n) : IsGreatest (diameterPairCounts n) n := by
  sorry

end Challenge223
