import Erdos336OrderExample

#print axioms erdos_336_example

/-- Erdős #336: `A = ⋃ (2^{2k}, 2^{2k+1}]` has order `2` but exact order `3`. -/
example : basisOrder A336 = 2 ∧ exactOrder A336 = 3 := erdos_336_example
