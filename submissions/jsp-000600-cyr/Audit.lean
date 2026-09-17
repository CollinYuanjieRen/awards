import Erdos732Designs

open Erdos732Upper

#print axioms Erdos732.erdos_732
#print axioms Erdos732Lower.erdos_732_lower
#print axioms Erdos732Upper.erdos_732_upper
#print axioms Erdos732Lower.exists_many_blockCompatible
#print axioms Erdos732Lower.completionDesign
#print axioms Erdos732Lower.count_completionDesign_blockSizes
#print axioms Erdos732Lower.line_inter_card_le_one
#print axioms Erdos732Lower.exp_le_pow
#print axioms Erdos732Upper.blockCompatible_replicate_two

/-- Erdős Problem 732, counting question: the number of block-compatible size multisets for `n`
is `exp(Θ(√n log n))` — at least `exp(c √n log n)` (Alon) and at most `exp(C √n log n)` (Erdős)
for all large `n`. -/
example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    {S : Multiset ℕ | BlockCompatible n S}.Finite ∧
      Real.exp (c * Real.sqrt n * Real.log n) ≤ ({S : Multiset ℕ | BlockCompatible n S}.ncard : ℝ) ∧
      ({S : Multiset ℕ | BlockCompatible n S}.ncard : ℝ) ≤ Real.exp (C * Real.sqrt n * Real.log n) :=
  Erdos732.erdos_732

/-- The lower bound alone (Alon, Theorem 2.3). -/
example : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    {S : Multiset ℕ | BlockCompatible n S}.Finite ∧
      Real.exp (c * Real.sqrt n * Real.log n) ≤ ({S : Multiset ℕ | BlockCompatible n S}.ncard : ℝ) :=
  Erdos732Lower.erdos_732_lower

/-- The upper bound alone (Erdős). -/
example : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    {S : Multiset ℕ | BlockCompatible n S}.Finite ∧
      ({S : Multiset ℕ | BlockCompatible n S}.ncard : ℝ) ≤ Real.exp (C * Real.sqrt n * Real.log n) :=
  Erdos732Upper.erdos_732_upper

/-- For every prime `p` with `p² ≤ n` there are `(p+1)^(p-2)` distinct block-compatible multisets. -/
example (p n : ℕ) [Fact p.Prime] (hn : p * p ≤ n) :
    ∃ f : (Fin (p - 2) → Fin (p + 1)) → Multiset ℕ,
      Function.Injective f ∧ ∀ m, BlockCompatible n (f m) :=
  Erdos732Lower.exists_many_blockCompatible p n hn

/-- Non-vacuity: `n.choose 2` copies of `2` are block-compatible for every `n`. -/
example (n : ℕ) : BlockCompatible n (Multiset.replicate (n.choose 2) 2) :=
  Erdos732Upper.blockCompatible_replicate_two n

-- The definitions, printed in full.
#print PairwiseBalancedDesign
#print PairwiseBalancedDesign.blockSizes
#print BlockCompatible
