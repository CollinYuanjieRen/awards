import Erdos574Cycles

open Filter Topology

#print axioms Erdos574.erdos_574
#print axioms Erdos574.not_claim_three
#print axioms Erdos574.exOddEven_lower
#print axioms Erdos574.le_exOddEven
#print axioms Erdos574.card_edgeFinset_doubled
#print axioms Erdos574.doubled_free_six
#print axioms Erdos574.doubled_free_five
#print axioms Erdos574.no_C6
#print axioms Erdos574.no_C4

/-- Erdős Problem 574 (Erdős–Simonovits), answered negatively: it is not true that
`ex(n; {C_{2k−1}, C_{2k}}) = (1 + o(1)) (n/2)^{1 + 1/k}` for every `k ≥ 2`. -/
example : ¬ ∀ k : ℕ, 2 ≤ k → Erdos574.Claim k := Erdos574.erdos_574

/-- The claim fails already for `k = 3`. -/
example : ¬ Tendsto (fun n : ℕ => (Erdos574.exOddEven n 3 : ℝ) / ((n : ℝ) / 2) ^ (1 + 1 / (3 : ℝ)))
    atTop (𝓝 1) :=
  Erdos574.not_claim_three

/-- The explicit lower bound: for every prime `q`, `ex(3q³; {C₅, C₆}) ≥ 2q⁴`. -/
example (q : ℕ) [Fact q.Prime] : 2 * q ^ 4 ≤ Erdos574.exOddEven (3 * q ^ 3) 3 :=
  Erdos574.exOddEven_lower q

/-- The definitions unfold as intended. -/
example (k : ℕ) : Erdos574.Claim k ↔ Tendsto
    (fun n : ℕ => (Erdos574.exOddEven n k : ℝ) / ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))) atTop (𝓝 1) :=
  Iff.rfl

/-- `Free` is non-induced subgraph containment: no injective homomorphism. -/
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    (SimpleGraph.cycleGraph 5).Free G ↔ ¬ SimpleGraph.IsContained (SimpleGraph.cycleGraph 5) G := Iff.rfl
