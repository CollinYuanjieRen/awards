import Mathlib

/-!
# Erdős Problem 673 — definitions

For `n ≥ 1` let `1 = d₁ < d₂ < ⋯ < d_{τ(n)} = n` be the divisors of `n` and
`G(n) = ∑_{1 ≤ i < τ(n)} dᵢ / dᵢ₊₁`. The consecutive pairs `(dᵢ, dᵢ₊₁)` are exactly the pairs
`(d, nextDiv n d)` for the divisors `d ≠ n`, where `nextDiv n d` is the least divisor of `n`
exceeding `d`; so `G n` is the finite sum below. "For almost all `n`" means: for every threshold
the exceptional set has natural density zero.
-/

namespace Erdos673

open Filter Topology

/-- The least divisor of `n` exceeding `d` (the next divisor after `d`). -/
noncomputable def nextDiv (n d : ℕ) : ℕ := sInf {e : ℕ | e ∣ n ∧ d < e}

/-- `G(n) = ∑_{d ∣ n, d ≠ n} d / nextDiv n d`, the sum of the ratios of consecutive divisors. -/
noncomputable def G (n : ℕ) : ℝ := ∑ d ∈ (Nat.divisors n).erase n, (d : ℝ) / nextDiv n d

open scoped Classical in
/-- A set of natural numbers has natural density zero. -/
def DensityZero (S : Set ℕ) : Prop :=
  Tendsto (fun X : ℕ => (((Finset.Icc 1 X).filter (· ∈ S)).card : ℝ) / X) atTop (𝓝 0)

end Erdos673
