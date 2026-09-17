/-
Comparator-style challenge module for JSP-000150 / Erdős Problem #151 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos151Challenge

open SimpleGraph

/-- `T` is a clique transversal of `G`: it contains at least one vertex of every maximal clique
of `G` on at least two vertices. -/
def IsCliqueTransversal {V : Type*} (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ s : Finset V, Maximal G.IsClique (s : Set V) → 2 ≤ s.card → ∃ v ∈ T, v ∈ s

/-- `τ(G)`: the minimal number of vertices meeting every maximal clique of `G` on at least two
vertices. -/
noncomputable def cliqueTransversalNum {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ T : Finset V, T.card = k ∧ IsCliqueTransversal G T}

/-- `H(n)`: the largest `h` such that every triangle-free graph on `n` vertices contains an
independent set on `h` vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {h : ℕ | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → h ≤ G.indepNum}

theorem not_exists_triangleFree_gt (n : ℕ) :
    ¬ ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ n - H n < cliqueTransversalNum G := by
  sorry

theorem cliqueTransversalNum_le_of_cliqueFree (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNum G ≤ n - H n := by
  sorry

theorem cliqueTransversalNum_le_card_sub_indepNum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : cliqueTransversalNum G ≤ Fintype.card V - G.indepNum := by
  sorry

theorem H_le_indepNum (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    H n ≤ G.indepNum := by
  sorry

theorem isCliqueTransversal_compl_of_isIndepSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hS : G.IsIndepSet (S : Set V)) :
    IsCliqueTransversal G (Finset.univ \ S) := by
  sorry

end Erdos151Challenge
