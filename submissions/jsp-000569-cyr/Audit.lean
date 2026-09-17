import Erdos698Sharp

open Erdos698

#print axioms Erdos698.erdos_698.variants.erdos_szekeres_sharp
#print axioms erdos_698_sharp_closed

/-- Erdős #698: the Erdős–Szekeres bound is sharp for `i = 1`, `j = p`, `n = 2p` (FC shape). -/
example (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (Nat.gcd ((2 * p).choose 1) ((2 * p).choose p) : ℝ) =
        ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) ∧
      ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) = (2 : ℝ) ^ 1 :=
  Erdos698.erdos_698.variants.erdos_szekeres_sharp p hp hp2
