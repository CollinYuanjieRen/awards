import Proof.Defs

/-!
# Erdős problem #287 — the sharpness example `1 = 1/2 + 1/3 + 1/6`

The problem page asks whether every representation `1 = 1/n₁ + ⋯ + 1/n_k` (`k ≥ 2`, distinct
`1 < n₁ < ⋯ < n_k`) has `max (n_{i+1} − n_i) ≥ 3`, and records that "the example
`1 = 1/2 + 1/3 + 1/6` shows that `3` would be best possible here".  This file proves that remark:
`[2, 3, 6]` is such a representation (T2), its maximal consecutive gap is `6 − 3 = 3` (T3), so a
representation with `k ≥ 2` terms and maximal gap exactly `3` exists (T4) and the inequality with
`3` replaced by `4` is false (T1, the audited root).

Not claimed here: the conjecture itself (`max (n_{i+1} − n_i) ≥ 3` for every representation), the
`≥ 2` half (Erdős 1932: `1` is not a sum of reciprocals of consecutive integers), and the conditional
statement on the page about primes `p` with `(p+1)/2` prime.
-/

namespace Erdos287

/-- (T2) `[2, 3, 6]` is a unit-fraction representation of `1`. -/
theorem unitFractionRep_example : UnitFractionRep [2, 3, 6] := by
  refine ⟨by decide, by decide, ?_⟩
  norm_num [List.map, List.sum_cons]

/-- (T3) Its maximal consecutive gap is `6 − 3 = 3`. -/
theorem maxGap_example : maxGap [2, 3, 6] = 3 := by
  decide

/-- (T4) The page's example, packaged: a representation with `k ≥ 2` terms whose maximal gap is
exactly `3`. -/
theorem exists_unitFractionRep_maxGap_eq_three :
    ∃ l : List ℕ, UnitFractionRep l ∧ 2 ≤ l.length ∧ maxGap l = 3 :=
  ⟨[2, 3, 6], unitFractionRep_example, by decide, maxGap_example⟩

/-- (T1) Audited root: the constant `3` of the problem cannot be raised to `4`. -/
theorem not_forall_four_le_maxGap :
    ¬ ∀ l : List ℕ, UnitFractionRep l → 2 ≤ l.length → 4 ≤ maxGap l := by
  intro h
  have := h [2, 3, 6] unitFractionRep_example (by decide)
  rw [maxGap_example] at this
  omega

end Erdos287
