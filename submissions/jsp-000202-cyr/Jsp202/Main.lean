import Jsp202.UpperBound
import Jsp202.ConstructionGeneral

/-!
# Hopf–Pannwitz theorem (planar diameter problem)

Combining the upper bound (`hopf_pannwitz_upper`) with the explicit lower-bound construction
(`exists_n_diameter_pairs`), we obtain the complete statement: among `n ≥ 3` points in the plane,
the maximum number of pairs at the diameter distance is exactly `n`.
-/

namespace HopfPannwitz

/-- The number of diameter (extremal-distance) pairs realizable by `n` planar points of diameter `D`,
as a set of possible counts. -/
def diameterPairCounts (n : ℕ) : Set ℕ :=
  {c | ∃ (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ),
      Function.Injective P ∧ (∀ i j, dist (P i) (P j) ≤ D) ∧
      (diameterGraph P D).edgeFinset.card = c}

/-- Hopf–Pannwitz (1934): among `n ≥ 3` points in the plane, the maximum number of pairs at the
diameter distance is exactly `n`. -/
theorem hopf_pannwitz (n : ℕ) (hn : 3 ≤ n) : IsGreatest (diameterPairCounts n) n := by
  constructor
  · -- membership: the explicit construction realizes exactly `n` diameter pairs
    obtain ⟨P, D, hinj, hUB, hcard⟩ := exists_n_diameter_pairs n hn
    exact ⟨P, D, hinj, hUB, hcard⟩
  · -- upper bound: every realizable count is at most `n`
    rintro c ⟨P, D, hinj, hUB, hcard⟩
    calc c = (diameterGraph P D).edgeFinset.card := hcard.symm
      _ ≤ n := hopf_pannwitz_upper n P hinj D hUB

end HopfPannwitz
