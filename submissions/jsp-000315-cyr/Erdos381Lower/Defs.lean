import ErdosProblems.Erdos381.Nicolas

/-!
# Erdős #381 (JSP-000315), lower bound: shared definitions

We reuse plby/lean-proofs' definitions verbatim (`Erdos381.tau`, `Erdos381.HighlyComposite`,
`Erdos381.Q`, `Erdos381.NicolasPolynomialUpperBound`) and add only what the lower bound needs.
-/

namespace Erdos381Lower

open Erdos381

/-- The largest prime factor of `n` (`0` for `n ≤ 1`). -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 0

/-- `(log n)^c` with a real exponent (plby's `logPower` uses natural exponents). -/
noncomputable def logRPower (c : ℝ) (n : ℕ) : ℝ := Real.log (n : ℝ) ^ c

end Erdos381Lower
