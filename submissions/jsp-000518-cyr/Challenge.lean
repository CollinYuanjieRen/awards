/- leanprover/lean4:v4.34.0-rc1  mathlib 1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d -/
/-
Comparator challenge for the JSP-000518 submission (Erdős Problem 637: distinct degrees in induced
subgraphs of Ramsey graphs — the Jenssen–Keevash–Long–Yepremyan `n^(2/3)` theorem, together with the
Bukh–Sudakov `n^(1/2)` theorem of plby/lean-proofs).  This module contains only statements proved by
`sorry` and imports only Mathlib, in the format of leanprover/comparator challenge modules.  The
definitions `Erdos88.neighborsIn`, `Erdos88.RamseyFree`, `Erdos637.degreeInto`,
`Erdos637.numDistinctDegrees` and `Erdos637.neighborhoodDiff` are copied verbatim (with their
surrounding `variable`/`open`/`noncomputable section` context) from plby/lean-proofs
`src/latest/ErdosProblems/Erdos88/Richness.lean`, `Erdos88/Foundations.lean` and `Erdos637.lean`
(commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e); `JKLY.Diverse` is copied verbatim from
`JSP518/JKLY/Diversity.lean`.  The solution module is `JSP518.JKLY.Main`.
-/

import Mathlib

open SimpleGraph

namespace Erdos88

universe u

noncomputable section

section Richness

variable {V : Type u} [Fintype V] [DecidableEq V]

def neighborsIn (G : SimpleGraph V) (v : V) (W : Finset V) : Finset V :=
  letI := Classical.decPred fun w ↦ G.Adj v w
  W.filter fun w ↦ G.Adj v w

end Richness

end

/-- The base-two version of `HomogeneousFree`, matching the `C`-Ramsey
terminology in Kwan--Sah--Sauermann--Sawhney. -/
def RamseyFree {n : ℕ} (C : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
      (S.card : ℝ) < C * Real.logb 2 n

end Erdos88

open scoped BigOperators symmDiff
open SimpleGraph

noncomputable section

namespace Erdos637

attribute [local instance] Classical.propDecidable

universe u

def degreeInto {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (W : Finset V) : ℕ :=
  (Erdos88.neighborsIn G v W).card

/-- The number of degree values occurring in the graph induced on `W`. -/
def numDistinctDegrees {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) : ℕ :=
  (W.image fun v ↦ degreeInto G v W).card

/-- The symmetric difference of the two ambient open neighbourhoods. -/
def neighborhoodDiff {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) : Finset V :=
  Erdos88.neighborsIn G x Finset.univ ∆
    Erdos88.neighborsIn G y Finset.univ

/-- Bukh–Sudakov (plby/lean-proofs, credited): a `C`-Ramsey graph has an induced subgraph on
`≫ n` vertices with `≫ n^(1/2)` distinct degrees. -/
theorem erdos_637 :
    ∀ C : ℝ, 0 < C →
      ∃ α : ℝ, 0 < α ∧
      ∃ β : ℝ, 0 < β ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
        Erdos88.RamseyFree C G →
          ∃ W : Finset (Fin n),
            α * (n : ℝ) ≤ W.card ∧
            β * Real.sqrt n ≤ numDistinctDegrees G W := by
  sorry

end Erdos637

end

namespace JKLY

universe u

/-- Pairwise ambient diversity of a vertex set. -/
def Diverse {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (δ : ℝ)
    (U : Finset V) : Prop :=
  ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' →
    δ * Fintype.card V ≤ ((Erdos637.neighborhoodDiff G u u').card : ℝ)

/-- JKLY Theorem 2: a `δ`-diverse set of size `n^(2/3)` forces `c · n^(2/3)` distinct degrees. -/
theorem jkly_theorem2 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
        ∀ (G : SimpleGraph V) (U : Finset V), Diverse G δ U →
          (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) ≤ U.card →
            ∃ W : Finset V,
              c * (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) ≤ Erdos637.numDistinctDegrees G W := by
  sorry

/-- JKLY Theorem 1: every `C`-Ramsey graph has an induced subgraph with `≫_C n^(2/3)` distinct
degrees. -/
theorem jkly_distinct_degrees (C : ℝ) (hC : 0 < C) : ∃ β : ℝ, 0 < β ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
      ∃ W : Finset (Fin n), β * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ Erdos637.numDistinctDegrees G W := by
  sorry

/-- Premise-free form: the Ramsey constant is `k + 1`. -/
theorem jkly_distinct_degrees_nat (k : ℕ) : ∃ β : ℝ, 0 < β ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree ((k : ℝ) + 1) G →
      ∃ W : Finset (Fin n),
        β * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ Erdos637.numDistinctDegrees G W := by
  sorry

end JKLY
