/-
Comparator-style challenge module for JSP-000847 / Erdős Problem #1017 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos1017Challenge

open SimpleGraph

/-- The unordered pairs of distinct elements of `T`. -/
def edgesOf {V : Type*} [DecidableEq V] (T : Finset V) : Finset (Sym2 V) :=
  T.sym2.filter (fun e => ¬ e.IsDiag)

/-- `P` partitions the edge set of `G` into edge-disjoint complete graphs. -/
def IsCliquePartition {V : Type*} [DecidableEq V] (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ S ∈ P, G.IsClique (S : Set V) ∧ 2 ≤ S.card) ∧ ∀ e ∈ G.edgeSet, ∃! S, S ∈ P ∧ e ∈ edgesOf S

/-- The clique partition number of `G`. -/
noncomputable def cliquePartitionNum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ P : Finset (Finset V), IsCliquePartition G P ∧ P.card = m}

/-- The page's `f(n, k)`. -/
noncomputable def f (n k : ℕ) : ℕ :=
  open scoped Classical in
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.edgeFinset.card = k ∧ cliquePartitionNum G = m}

/-- The balanced complete bipartite graph on `Fin n`. -/
def balancedBipartite (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => i.val < n / 2 ∧ n / 2 ≤ j.val)

instance (n : ℕ) : DecidableRel (balancedBipartite n).Adj := fun i j => by
  unfold balancedBipartite; infer_instance

theorem sq_div_four_le_f (n : ℕ) : n ^ 2 / 4 ≤ f n (n ^ 2 / 4) := by
  sorry

theorem cliquePartitionNum_balancedBipartite (n : ℕ) :
    cliquePartitionNum (balancedBipartite n) = n ^ 2 / 4 := by
  sorry

theorem card_edgeFinset_balancedBipartite (n : ℕ) :
    (balancedBipartite n).edgeFinset.card = n ^ 2 / 4 := by
  sorry

theorem cliquePartitionNum_eq_of_cliqueFree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    cliquePartitionNum G = G.edgeFinset.card := by
  sorry

theorem cliquePartitionNum_le_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : cliquePartitionNum G ≤ G.edgeFinset.card := by
  sorry

theorem balancedBipartite_cliqueFree_three (n : ℕ) : (balancedBipartite n).CliqueFree 3 := by
  sorry

end Erdos1017Challenge
