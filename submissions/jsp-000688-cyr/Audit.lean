import Erdos832Fano

open Erdos832

#print axioms erdos_832_fano_closed
#print axioms Erdos832.erdos_832_false_three_three

/-- Erdős #832: the Fano plane has chromatic number `3` and fewer than `C(5, 3)` edges. -/
example : fano.HasChromaticNumber 3 ∧ fano.edges.card < ((3 - 1) * (3 - 1) + 1).choose 3 :=
  ⟨erdos_832_fano_closed.2.2.2.1, erdos_832_fano_closed.2.2.2.2⟩
