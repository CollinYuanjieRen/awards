import Erdos380BadIntervals

open Erdos380

#print axioms erdos_380_tao_closed
#print axioms Erdos380.lt_two_mul_of_isBad

/-- Erdős #380, Tao: a bad interval satisfies `v < 2u`. -/
example {u v : ℕ} (hb : IsBad u v) : v < 2 * u := lt_two_mul_of_isBad hb
