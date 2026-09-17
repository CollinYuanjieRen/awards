import Proof.Bound

/-!
# Erdős problem #181 — the hypercube and graph Ramsey numbers: definitions

This module fixes the frozen definitions used by the scoped component of Erdős problem #181
(the page's trivial bound `R(Q_n) ≤ R(K_{2^n}) ≤ C^{2^n}`).

* `Erdos181.hypercube n` is the `n`-dimensional hypercube graph `Q_n` on the `2^n` vertices
  `Fin n → Bool`, two vertices being adjacent when they differ in exactly one coordinate;
* `Erdos181.GraphRamseyProp N G` says that every red/blue colouring of `K_N` (a
  `SimpleGraph (Fin N)`, red = edges, blue = non-edges) contains a monochromatic copy of `G`
  (Mathlib's `G ⊑ R`: an injective graph homomorphism);
* `Erdos181.graphRamsey G` is the graph Ramsey number `R(G)`, the least such `N`.

The two-colour Ramsey numbers `r(m, n)` and `R(n) = r(n, n)` come from our own Ramsey toolbox
(`Proof.RamseyDefs`, `Proof.Ramsey`, `Proof.Bound`).
-/

namespace Erdos181

open SimpleGraph

/-- The `n`-dimensional hypercube graph `Q_n`: vertices are the `2^n` vectors `Fin n → Bool`,
and two vertices are adjacent when they differ in exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun u v => ∃ i, u i ≠ v i ∧ ∀ j, j ≠ i → u j = v j)

/-- Every red/blue colouring of `K_N` contains a red or a blue copy of `G`. -/
def GraphRamseyProp {V : Type*} (N : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ G ⊑ Rᶜ

/-- The graph Ramsey number `R(G)`: the least `N` such that every red/blue colouring of `K_N`
contains a monochromatic copy of `G`.  The set is nonempty for every graph on a finite vertex
type (`Erdos181.graphRamseyProp_ramsey`), so the `sInf` is honest. -/
noncomputable def graphRamsey {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | GraphRamseyProp N G}

end Erdos181
