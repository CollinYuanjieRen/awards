/-
Comparator-style challenge module for JSP-000508 / Erdős Problem #627 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Shift.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos627Challenge

/-- The vertices of the shift graph on `{0, …, N-1}`: ordered pairs `(i, j)` with `i < j`. -/
def ShiftVertex (N : ℕ) : Type := {p : Fin N × Fin N // p.1 < p.2}

/-- The shift graph: `(i, j)` is adjacent to `(j, l)` (in either order). -/
def shiftGraph (N : ℕ) : SimpleGraph (ShiftVertex N) :=
  SimpleGraph.fromRel (fun p q => p.1.2 = q.1.1)

theorem exists_cliqueFree_chromatic (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.CliqueFree 3 ∧ G.chromaticNumber = (k : ℕ∞) := by
  sorry

theorem exists_cliqueNum_two_chromatic (k : ℕ) (hk : 2 ≤ k) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.CliqueFree 3 ∧ (∃ u v, G.Adj u v) ∧ G.chromaticNumber = (k : ℕ∞) := by
  sorry

theorem shiftGraph_cliqueFree (N : ℕ) : (shiftGraph N).CliqueFree 3 := by
  sorry

theorem shiftGraph_chromaticNumber (k : ℕ) : (shiftGraph (2 ^ k)).chromaticNumber = (k : ℕ∞) := by
  sorry

theorem shiftGraph_cliqueNum (k : ℕ) (hk : 2 ≤ k) : (shiftGraph (2 ^ k)).cliqueNum = 2 := by
  sorry

end Erdos627Challenge
