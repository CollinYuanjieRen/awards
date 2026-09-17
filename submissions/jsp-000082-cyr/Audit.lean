import Erdos64InfiniteTree

open SimpleGraph

#print axioms ternaryTree_isAcyclic
#print axioms erdos_64_infinite_counterexample

/-- Erdős #64: an infinite graph with all degrees `≥ 3`, acyclic, with no cycle of length `2^k`. -/
example : ∃ (V : Type) (G : SimpleGraph V), Infinite V ∧
    (∀ v : V, ∃ s : Finset V, (∀ w, G.Adj v w ↔ w ∈ s) ∧ 3 ≤ s.card) ∧
    G.IsAcyclic ∧
    ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k :=
  erdos_64_infinite_counterexample
