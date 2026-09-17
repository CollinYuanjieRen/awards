import Proof.Bound

/-!
# Erdős problem #87 — graph Ramsey numbers: definitions

Reused from our own JSP-000175 package (Erdős #181), where the graph Ramsey number `R(G)` was
introduced; the hypercube of that package is not needed here and is omitted.

* `Erdos87.GraphRamseyProp N G` says that every red/blue colouring of `K_N` (a
  `SimpleGraph (Fin N)`, red = edges, blue = non-edges) contains a monochromatic copy of `G`
  (Mathlib's `G ⊑ R`: an injective graph homomorphism);
* `Erdos87.graphRamsey G` is the graph Ramsey number `R(G)`, the least such `N`.

The two-colour Ramsey numbers `r(m, n)` and `R(n) = r(n, n)` come from our own Ramsey toolbox
(`Proof.RamseyDefs`, `Proof.Ramsey`, `Proof.Bound`).
-/

namespace Erdos87

open SimpleGraph

/-- Every red/blue colouring of `K_N` contains a red or a blue copy of `G`. -/
def GraphRamseyProp {V : Type*} (N : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ G ⊑ Rᶜ

/-- The graph Ramsey number `R(G)`: the least `N` such that every red/blue colouring of `K_N`
contains a monochromatic copy of `G`.  The set is nonempty for every graph on a finite vertex
type (`Erdos87.graphRamseyProp_ramsey`, reused from JSP-000175), so the `sInf` is honest. -/
noncomputable def graphRamsey {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | GraphRamseyProp N G}

end Erdos87
