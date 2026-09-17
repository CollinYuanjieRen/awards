import Mathlib

/-!
# Erdős problem #901 — Property B and `m(n)`: definitions

Erdős problem #901 asks to estimate `m(n)`, the least number of edges of an `n`-uniform hypergraph
that is `3`-chromatic, i.e. that has no *Property B*: no `2`-colouring of the vertices makes every
edge bichromatic.  This module fixes the definitions.

* `Erdos901.IsUniform n E` — every edge of `E` has exactly `n` vertices;
* `Erdos901.TwoColorable E` — some `2`-colouring `c : V → Bool` makes every edge of `E` contain
  two vertices of different colours (Property B);
* `Erdos901.m n` — the least number of edges of an `n`-uniform hypergraph (on some finite vertex
  set `Fin N`) that is not `2`-colourable.  The set is nonempty for every `n`
  (`Erdos901.exists_not_twoColorable`), so the `sInf` is honest.
-/

namespace Erdos901

/-- Every edge of `E` has exactly `n` vertices. -/
def IsUniform {V : Type*} (n : ℕ) (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, e.card = n

/-- Property B: some `2`-colouring of the vertices makes every edge bichromatic. -/
def TwoColorable {V : Type*} (E : Finset (Finset V)) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ E, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- `m(n)`: the least number of edges of an `n`-uniform hypergraph without Property B
(a `3`-chromatic `n`-uniform hypergraph). -/
noncomputable def m (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ (N : ℕ) (E : Finset (Finset (Fin N))), IsUniform n E ∧ ¬ TwoColorable E ∧ E.card = k}

end Erdos901
