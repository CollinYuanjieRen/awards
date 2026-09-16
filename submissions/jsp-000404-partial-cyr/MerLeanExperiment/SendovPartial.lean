import MerLeanExperiment.Small
import MerLeanExperiment.SharpUpper
import MerLeanExperiment.DyadicLower
import MerLeanExperiment.FivePointLower
import MerLeanExperiment.SixPointLower

/-!
# Erdős problem #504 (Blumenthal / Sendov minimax angle) — the unconditionally proved part

`PlanarMinimax.SendovAnswer` (in `Problem.lean`) is the full Sendov (1995) classification of
`minimaxAngle n`.  Its two general sharp *lower* branches for `n` that is not a dyadic endpoint
depend on Sendov's 1995 Lemma 4.1, whose `s ≥ 4` capacity maximum is asserted without a correct
proof in the literature (documented in the submission notes); that part is therefore left open and
is **not** claimed.

This file collects everything that *is* proved unconditionally in this development, with the exact
definitions of `Problem.lean`:

* the exact minimax angle for every small cardinality `3 ≤ n ≤ 8`;
* the exact minimax angle at every dyadic endpoint `n = 2^k`, `k ≥ 2`;
* both of Sendov's construction (upper) bounds, over the exact intervals of `SendovAnswer`,
  for every `m ≥ 2`.
-/

namespace PlanarMinimax

/-- The unconditionally established portion of the Sendov minimax-angle classification. -/
theorem sendov_partial :
    -- exact small cardinalities `n = 3, 4`
    (minimaxAngle 3 = Real.pi / 3 ∧ minimaxAngle 4 = Real.pi / 2) ∧
    -- exact value `n = 5`
    minimaxAngle 5 = 3 * Real.pi / 5 ∧
    -- exact value `6 ≤ n ≤ 8`
    (∀ N : ℕ, 6 ≤ N → N ≤ 8 → minimaxAngle N = 2 * Real.pi / 3) ∧
    -- exact value at every dyadic endpoint `n = 2^k`, `k ≥ 2`
    (∀ k : ℕ, 2 ≤ k → minimaxAngle (2 ^ k) = Real.pi * (1 - 1 / (k : ℝ))) ∧
    -- both construction (upper) bounds for every `m ≥ 2`, over the exact `SendovAnswer` intervals
    ((∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
        2 ^ m < n → n ≤ 2 ^ m + 2 ^ (m - 2) →
          minimaxAngle n ≤ Real.pi * (1 - 2 / (2 * (m : ℝ) + 1))) ∧
     (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ,
        2 ^ m + 2 ^ (m - 2) < n → n ≤ 2 ^ (m + 1) →
          minimaxAngle n ≤ Real.pi * (1 - 1 / ((m : ℝ) + 1)))) :=
  ⟨small_cardinalities, minimaxAngle_five,
    fun _ hN6 hN8 => minimaxAngle_six_to_eight hN6 hN8,
    fun _ hk => minimaxAngle_dyadic hk, sendov_upper_bounds⟩

#print axioms sendov_partial

end PlanarMinimax
