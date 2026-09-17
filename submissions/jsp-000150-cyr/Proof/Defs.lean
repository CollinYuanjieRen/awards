import Mathlib

/-!
# Clique transversals of triangle-free graphs: definitions

This module fixes the frozen definitions used by the scoped component of Erdős problem #151
(the page's remark that a triangle-free graph `G` on `n` vertices has clique transversal
number `τ(G) ≤ n − H(n)`).

* `Erdos151.IsCliqueTransversal G T` — `T` meets every maximal clique of `G` on at least two
  vertices (maximal cliques are Mathlib's `Maximal G.IsClique`);
* `Erdos151.cliqueTransversalNum G` — `τ(G)`, the least size of a clique transversal;
* `Erdos151.H n` — the largest `h` such that every triangle-free graph on `n` vertices has an
  independent set on `h` vertices (independence number `SimpleGraph.indepNum`).
-/

namespace Erdos151

open SimpleGraph

/-- `T` is a clique transversal of `G`: it contains at least one vertex of every maximal clique
of `G` on at least two vertices. -/
def IsCliqueTransversal {V : Type*} (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ s : Finset V, Maximal G.IsClique (s : Set V) → 2 ≤ s.card → ∃ v ∈ T, v ∈ s

/-- `τ(G)`: the minimal number of vertices meeting every maximal clique of `G` on at least two
vertices.  The set is nonempty (`Finset.univ` is a transversal, `Erdos151.isCliqueTransversal_univ`),
so the `sInf` is honest. -/
noncomputable def cliqueTransversalNum {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ T : Finset V, T.card = k ∧ IsCliqueTransversal G T}

/-- `H(n)`: the largest `h` such that every triangle-free graph on `n` vertices contains an
independent set on `h` vertices.  The set is nonempty (`0`) and bounded above (by the independence
number of the edgeless graph), so the `sSup` is attained (`Erdos151.H_le_indepNum`). -/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {h : ℕ | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → h ≤ G.indepNum}

end Erdos151
