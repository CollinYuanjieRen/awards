import Erdos856DoubleCounting

open Erdos856

#print axioms erdos_856_double_counting_closed
#print axioms Erdos856.card_solutions_lt

/-- Erdős #856: fewer than `k` solutions of `t = a p` for every `t`. -/
example {k : ℕ} {A : Finset ℕ} (hA : NoEqualLcm k A) (t : ℕ) : (solutions A t).card < k :=
  card_solutions_lt hA t
