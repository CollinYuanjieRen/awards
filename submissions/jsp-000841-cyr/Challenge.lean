/-
Comparator-style challenge module for JSP-000841 / Erdős Problem #1011 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
`Proof/Main.lean` (the definition below is the one of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

open Finset SimpleGraph

namespace Erdos1011Challenge

/-- Erdős's `f₃(n)`: the least `m` such that every graph on `n` vertices with at least `m` edges and
chromatic number at least `3` (i.e. not `2`-colourable) contains a triangle. -/
noncomputable def f3 (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.Colorable 2 → m ≤ G.edgeSet.ncard → ¬ G.CliqueFree 3}

theorem f3_eq (n : ℕ) (hn : 5 ≤ n) : f3 n = (n - 1) ^ 2 / 4 + 2 := by
  sorry

theorem edges_le_of_cliqueFree_of_not_colorable (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) (hb : ¬ G.Colorable 2) : G.edgeSet.ncard ≤ (n - 1) ^ 2 / 4 + 1 := by
  sorry

theorem exists_extremal (n : ℕ) (hn : 5 ≤ n) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ ¬ G.Colorable 2 ∧
      G.edgeSet.ncard = (n - 1) ^ 2 / 4 + 1 := by
  sorry

end Erdos1011Challenge
