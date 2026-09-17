import Erdos123Counterexample

open Submonoid
open scoped Pointwise

#print axioms erdos_123_no_common_factor_counterexample
#print axioms Erdos123.not_isDComplete_six_ten_fifteen

/-- Erdős #123: `{6^k 10^l 15^m}` is not `d`-complete. -/
example : ¬ Erdos123.IsDComplete (↑(powers 6) * ↑(powers 10) * ↑(powers 15) : Set ℕ) :=
  erdos_123_no_common_factor_counterexample.2
