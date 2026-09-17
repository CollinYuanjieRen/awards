import Erdos409OneInfinite

open scoped Topology ArithmeticFunction.sigma Nat
open Filter

#print axioms erdos_409_F_eq_one_infinite
#print axioms erdos_409_F_eq_one_not_finite

/-- Erdős #409: `F(n) = 1` for infinitely many `n`. -/
example : { n : ℕ | IsLeast { i | ((φ · + 1)^[i] n).Prime } 1 }.Infinite := erdos_409_F_eq_one_infinite
