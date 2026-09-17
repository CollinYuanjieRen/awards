import Mathlib

/-! Comparator-style challenge module (Mathlib-only; target with `sorry`, not imported by the build)
for JSP-000671 / Erdős #814, the size-uncapped k-core existence. -/

namespace Challenge814

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S` induces a subgraph of minimum degree ≥ `k`. -/
def InducedMinDegGe (G : SimpleGraph V) (k : ℕ) (S : Finset V) : Prop :=
  ∀ v ∈ S, k ≤ (S.filter (fun w => G.Adj v w)).card

/-- A graph with more than `(k-1)·n` edges contains a nonempty induced subgraph of min degree ≥ `k`. -/
theorem exists_core (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : (k - 1) * Fintype.card V < G.edgeFinset.card) :
    ∃ S : Finset V, S.Nonempty ∧ InducedMinDegGe G k S := by
  sorry

end Challenge814
