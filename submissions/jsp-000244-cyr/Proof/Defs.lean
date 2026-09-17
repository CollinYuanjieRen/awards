import Mathlib

/-!
# Erdős problem #287 — unit-fraction representations of `1` and consecutive gaps: definitions

The problem page asks whether every representation `1 = 1/n₁ + ⋯ + 1/n_k` (with `k ≥ 2` and distinct
integers `1 < n₁ < ⋯ < n_k`) must have `max (n_{i+1} − n_i) ≥ 3`, and records the sharpness example
`1 = 1/2 + 1/3 + 1/6`.  This module fixes the definitions used to state that example.

* `Erdos287.UnitFractionRep l` — the list `l = [n₁, …, n_k]` is strictly increasing, starts above `1`,
  and its reciprocals sum to `1` (in `ℚ`);
* `Erdos287.maxGap l` — the maximum of the consecutive differences `n_{i+1} − n_i` (`0` for a list
  with fewer than two entries).
-/

namespace Erdos287

/-- `l = [n₁, …, n_k]` is a representation of `1` by distinct unit fractions with denominators
`1 < n₁ < ⋯ < n_k`. -/
def UnitFractionRep (l : List ℕ) : Prop :=
  l.IsChain (· < ·) ∧ 1 < l.headI ∧ (l.map (fun n => (n : ℚ)⁻¹)).sum = 1

/-- The maximal consecutive gap `max (n_{i+1} − n_i)` of a list `[n₁, …, n_k]`. -/
def maxGap (l : List ℕ) : ℕ :=
  ((l.zip l.tail).map (fun p => p.2 - p.1)).foldr max 0

end Erdos287
