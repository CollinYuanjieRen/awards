/-
Comparator-style challenge module for JSP-000660 / Erdős Problem #803.

This file is intentionally self-contained: it depends on Mathlib only and states the three
root results of `Proof.Main` with `sorry`, so the statements can be compared mechanically
with those proved in `Proof/Main.lean` (the definitions below are the ones of `Proof/Defs.lean`
and are repeated verbatim).  Nothing in this file is used by the proof.
-/
import Mathlib

open Finset

namespace Erdos803Challenge

variable {V : Type*}

/-- Degree of `v` inside the subgraph `H` (the number of `H`-neighbours of `v`). -/
noncomputable def sdeg {G : SimpleGraph V} (H : G.Subgraph) (v : V) : ℕ :=
  (H.neighborSet v).ncard

/-- `H` is `D`-balanced: every degree is at most `D` times every other degree. -/
def Balanced {G : SimpleGraph V} (D : ℝ) (H : G.Subgraph) : Prop :=
  ∀ v ∈ H.verts, ∀ w ∈ H.verts, (sdeg H v : ℝ) ≤ D * sdeg H w

/-- The Erdős–Simonovits question, "at least `m₀` vertices" reading. -/
def ErdosSimonovitsUniform (ε D : ℝ) : Prop :=
  ∀ m₀ : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    (n : ℝ) * Real.logb 2 n ≤ G.edgeSet.ncard →
      ∃ H : G.Subgraph, m₀ ≤ H.verts.ncard ∧ Balanced D H ∧
        ε * H.verts.ncard * Real.logb 2 H.verts.ncard ≤ H.edgeSet.ncard

/-- The Erdős–Simonovits question, literal "exactly `m` vertices" reading. -/
def ErdosSimonovitsLiteral (ε D : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    (n : ℝ) * Real.logb 2 n ≤ G.edgeSet.ncard →
      ∃ H : G.Subgraph, H.verts.ncard = m ∧ Balanced D H ∧
        ε * m * Real.logb 2 m ≤ H.edgeSet.ncard

theorem alon_construction (D : ℝ) (hD : 1 ≤ D) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ G : SimpleGraph (Fin N),
      (N : ℝ) * Real.logb 2 N ≤ G.edgeSet.ncard ∧
        ∀ H : G.Subgraph, Balanced D H →
          (H.edgeSet.ncard : ℝ) ≤ 18 * H.verts.ncard *
            (4 * Real.sqrt (Real.logb 2 H.verts.ncard) + Real.logb 2 (64 * D) + 26) := by
  sorry

theorem not_erdosSimonovitsUniform :
    ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsUniform ε D := by
  sorry

theorem not_erdosSimonovitsLiteral :
    ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsLiteral ε D := by
  sorry

end Erdos803Challenge
