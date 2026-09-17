import Mathlib

/-!
# Erdős problem #1017 — clique partitions: definitions

Erdős problem #1017 concerns `f(n, k)`, the least number such that every graph on `n` vertices
and `k` edges can be partitioned into at most `f(n, k)` edge-disjoint complete graphs (the clique
partition number).  Erdős, Goodman and Pósa proved `f(n, k) ≤ n²/4`, and the problem page records
that this "is best possible in general, as witnessed for example by a complete bipartite graph".
This module fixes the definitions used to state that sharpness remark.

* `Erdos1017.edgesOf T` — the unordered pairs of distinct elements of `T` (reused from our own
  JSP-000164 package, Erdős #167);
* `Erdos1017.IsCliquePartition G P` — the parts of `P` are cliques of `G` on at least two vertices
  and every edge of `G` lies in exactly one part (a partition of `E(G)` into edge-disjoint complete
  graphs; parts carrying no edge are excluded so that the count is honest);
* `Erdos1017.cliquePartitionNum G` — the least number of parts of a clique partition of `G`;
* `Erdos1017.f n k` — the page's `f(n, k)`: the largest clique partition number of a graph on
  `n` vertices with `k` edges;
* `Erdos1017.balancedBipartite n` — the complete bipartite graph on `Fin n` with parts
  `{i < n/2}` and `{i ≥ n/2}`, which has `⌊n²/4⌋` edges.
-/

namespace Erdos1017

open SimpleGraph

/-- `edgesOf T` is the set of unordered pairs of distinct elements of `T`, i.e. the edges spanned
by `T` in a complete graph. -/
def edgesOf {V : Type*} [DecidableEq V] (T : Finset V) : Finset (Sym2 V) :=
  T.sym2.filter (fun e => ¬ e.IsDiag)

/-- `P` partitions the edge set of `G` into edge-disjoint complete graphs: every part is a clique
of `G` on at least two vertices, and every edge of `G` lies in exactly one part. -/
def IsCliquePartition {V : Type*} [DecidableEq V] (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ S ∈ P, G.IsClique (S : Set V) ∧ 2 ≤ S.card) ∧ ∀ e ∈ G.edgeSet, ∃! S, S ∈ P ∧ e ∈ edgesOf S

/-- The clique partition number of `G`: the least number of edge-disjoint complete graphs
partitioning its edge set.  The set is nonempty (the edges themselves form a clique partition,
`Erdos1017.cliquePartitionNum_le_card_edgeFinset`), so the `sInf` is honest. -/
noncomputable def cliquePartitionNum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ P : Finset (Finset V), IsCliquePartition G P ∧ P.card = m}

/-- The page's `f(n, k)`: the least number of edge-disjoint complete graphs that suffices for
every graph on `n` vertices with `k` edges, i.e. the largest clique partition number of such a
graph.  The set is bounded by `k` (each graph is partitioned by its own edges), so the `sSup` is
honest; it is empty (value `0`) when no graph on `n` vertices has `k` edges. -/
noncomputable def f (n k : ℕ) : ℕ :=
  open scoped Classical in
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.edgeFinset.card = k ∧ cliquePartitionNum G = m}

/-- The balanced complete bipartite graph on `Fin n`: `i` and `j` are adjacent when one of them is
below `n / 2` and the other is not. -/
def balancedBipartite (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => i.val < n / 2 ∧ n / 2 ≤ j.val)

instance (n : ℕ) : DecidableRel (balancedBipartite n).Adj := fun i j => by
  unfold balancedBipartite; infer_instance

end Erdos1017
