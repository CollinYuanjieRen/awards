import Erdos389Examples

#print axioms erdos_389_two_five
#print axioms erdos_389_three_four
#print axioms erdos_389_examples_closed

/-- Erdős #389: the page's examples, with minimality of `k`. -/
example : IsLeast {k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (2 + i) ∣ ∏ i ∈ Finset.range k, (2 + k + i)} 5 :=
  erdos_389_two_five
example : IsLeast {k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (3 + i) ∣ ∏ i ∈ Finset.range k, (3 + k + i)} 4 :=
  erdos_389_three_four
