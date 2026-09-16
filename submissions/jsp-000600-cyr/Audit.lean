import Proof

open Erdos732Upper

#print axioms Erdos732Upper.erdos_732_upper
#print axioms Erdos732Upper.blockCompatible_replicate_two

example :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      {S : Multiset ℕ | BlockCompatible n S}.Finite ∧
        (({S : Multiset ℕ | BlockCompatible n S}.ncard : ℝ) ≤
          Real.exp (C * Real.sqrt n * Real.log n)) :=
  Erdos732Upper.erdos_732_upper

example (n : ℕ) : BlockCompatible n (Multiset.replicate (n.choose 2) 2) :=
  Erdos732Upper.blockCompatible_replicate_two n

#print PairwiseBalancedDesign
#print PairwiseBalancedDesign.blockSizes
#print BlockCompatible
