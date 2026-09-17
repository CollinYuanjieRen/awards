import MerLeanExperiment.Ramsey

/-!
# Erdős problem #551 — asymmetric graph Ramsey numbers and the blow-up colouring: definitions

Erdős problem #551 (Erdős–Faudree–Rousseau–Schelp) asks to prove `R(C_k, K_n) = (k − 1)(n − 1) + 1`
for `k ≥ n ≥ 3` (except `k = n = 3`).  This module fixes the definitions used to state the lower
half of that identity, which holds for all `k, n ≥ 1` by the standard blow-up colouring.

* `Erdos551.GraphRamseyProp N G H` — every red/blue colouring of `K_N` (a `SimpleGraph (Fin N)`,
  red = edges, blue = non-edges) contains a red copy of `G` or a blue copy of `H` (Mathlib's
  `⊑`, an injective graph homomorphism);
* `Erdos551.graphRamsey G H` — the asymmetric graph Ramsey number `R(G, H)`, the least such `N`;
  the set is nonempty for graphs on finite vertex types (`Erdos551.graphRamseyProp_ramsey`,
  from our own two-colour Ramsey toolbox), so the `sInf` is honest;
* `Erdos551.blowUp a b` — the colouring of `K_{a·b}` whose vertices are `Fin a × Fin b` (block,
  position) with an edge red exactly when both endpoints lie in the same block: `a` red cliques of
  size `b`, all other pairs blue.
-/

namespace Erdos551

open SimpleGraph

/-- Every red/blue colouring of `K_N` contains a red copy of `G` or a blue copy of `H`. -/
def GraphRamseyProp {α β : Type*} (N : ℕ) (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ H ⊑ Rᶜ

/-- The asymmetric graph Ramsey number `R(G, H)`: the least `N` such that every red/blue colouring
of `K_N` contains a red copy of `G` or a blue copy of `H`. -/
noncomputable def graphRamsey {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {N : ℕ | GraphRamseyProp N G H}

/-- The blow-up colouring: `a` disjoint red cliques of size `b` (the blocks `Fin a × {i}`), blue
between blocks. -/
def blowUp (a b : ℕ) : SimpleGraph (Fin a × Fin b) :=
  SimpleGraph.fromRel (fun x y => x.1 = y.1)

end Erdos551
