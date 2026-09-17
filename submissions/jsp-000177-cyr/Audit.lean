import Erdos183Recurrence

open Erdos183

#print axioms erdos_183_recurrence_closed
#print axioms Erdos183.erdos_183_recurrence

/-- Erdős #183: the pigeonhole recurrence. -/
example (k : ℕ) (hk : 1 ≤ k) :
    multicolourTriangleRamsey k ≤ 2 + k * (multicolourTriangleRamsey (k - 1) - 1) :=
  erdos_183_recurrence k hk
