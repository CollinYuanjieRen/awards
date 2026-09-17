import Mathlib

/-!
# Erdős Problem #542: the sharpness example `A = {2, 3, 5}`

Erdős asked whether `∑_{a ∈ A} 1/a ≤ 31/30` for every `A ⊆ {1, …, n}` with `lcm(a, b) > n` for all
distinct `a, b ∈ A` (SOLVED by Schinzel–Szekeres; that theorem and the second question are NOT
formalized here).  The problem page records: "The first bound is best possible as `A = {2, 3, 5}`
demonstrates", and that Erdős, Schinzel and Szekeres conjectured that `2, 3, 5` and `3, 4, 5, 7, 11`
are the only two such sequences with sum `> 1`.  This file verifies the two examples: for
`n = 5`, `A = {2, 3, 5} ⊆ {1, …, 5}` has all pairwise lcms `> 5` and reciprocal sum exactly
`31/30`; for `n = 11`, `A = {3, 4, 5, 7, 11} ⊆ {1, …, 11}` has all pairwise lcms `> 11` and
reciprocal sum `4699/4620 > 1`.  (The conjecture that these are the only two is not claimed.)
There is no formal-conjectures rendering of this problem; the statements are ours.
-/

namespace Erdos542

/-- `A ⊆ {1, …, n}` with `lcm(a, b) > n` for all distinct `a, b ∈ A`: the hypothesis of the
problem. -/
def IsLcmLarge (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b

/-- `A = {2, 3, 5}` for `n = 5`: admissible, with reciprocal sum `31/30`. -/
theorem two_three_five :
    IsLcmLarge 5 {2, 3, 5} ∧ ∑ a ∈ ({2, 3, 5} : Finset ℕ), (1 : ℚ) / a = 31 / 30 := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-- `A = {3, 4, 5, 7, 11}` for `n = 11`: admissible, with reciprocal sum `4699/4620 > 1`. -/
theorem three_four_five_seven_eleven :
    IsLcmLarge 11 {3, 4, 5, 7, 11} ∧
      ∑ a ∈ ({3, 4, 5, 7, 11} : Finset ℕ), (1 : ℚ) / a = 4699 / 4620 ∧
      1 < ∑ a ∈ ({3, 4, 5, 7, 11} : Finset ℕ), (1 : ℚ) / a := by
  have hsum : ∑ a ∈ ({3, 4, 5, 7, 11} : Finset ℕ), (1 : ℚ) / a = 4699 / 4620 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  refine ⟨⟨by decide, by decide⟩, hsum, ?_⟩
  rw [hsum]
  norm_num

end Erdos542

open Erdos542 in
/-- **Erdős #542, the sharpness example, closed form**: `{2, 3, 5}` is admissible for `n = 5`
with reciprocal sum `31/30`, and `{3, 4, 5, 7, 11}` is admissible for `n = 11` with reciprocal sum
`4699/4620 > 1`. -/
theorem erdos_542_examples_closed :
    (IsLcmLarge 5 {2, 3, 5} ∧ ∑ a ∈ ({2, 3, 5} : Finset ℕ), (1 : ℚ) / a = 31 / 30) ∧
      (IsLcmLarge 11 {3, 4, 5, 7, 11} ∧
        ∑ a ∈ ({3, 4, 5, 7, 11} : Finset ℕ), (1 : ℚ) / a = 4699 / 4620 ∧
        1 < ∑ a ∈ ({3, 4, 5, 7, 11} : Finset ℕ), (1 : ℚ) / a) := by
  exact ⟨Erdos542.two_three_five, Erdos542.three_four_five_seven_eleven⟩
