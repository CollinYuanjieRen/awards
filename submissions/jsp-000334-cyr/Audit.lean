import Erdos407Identities

open Erdos407

#print axioms erdos_407_identities_closed
#print axioms Erdos407.erdos_407_infinite_four

/-- Erdős #407: infinitely many `n` have at least four representations. -/
example : {n : ℕ | 4 ≤ w n}.Infinite := erdos_407_identities_closed.2
