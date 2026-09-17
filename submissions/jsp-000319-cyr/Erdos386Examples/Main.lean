import Mathlib

/-!
# Erdős Problem #386: Weisenberg's examples and the known `C(n, 2)` values

Erdős and Graham asked whether `C(n, k)` (`2 ≤ k ≤ n − 2`) can be a product of consecutive primes
infinitely often (OPEN; not addressed here), writing that "probably this can never happen for
`C(n, k)` if `3 ≤ k ≤ n − 3`".  The problem page records that "Weisenberg has provided four easy
examples that show Erdős and Graham were too optimistic here: `C(7,3) = 5·7`,
`C(10,4) = 2·3·5·7`, `C(14,4) = 7·11·13`, `C(15,6) = 5·7·11·13`.  The known values of `n` for which
`C(n,2)` is the product of consecutive primes are `4, 6, 15, 21, 715`."

This file verifies these facts in the shape of the formal-conjectures statement `erdos_386`,
where "product of consecutive primes" is `∃ p q, m = ∏ i ∈ Finset.Ico p q, Nat.nth Nat.Prime i`
(`Nat.nth Nat.Prime i` is the `i`-th prime, `2, 3, 5, …`).  The list `4, 6, 15, 21, 715` is only
claimed as *known* examples (membership), not as complete; the main question is not claimed.
-/

namespace Erdos386

open Nat

/-- The formal-conjectures notion: `m` is a product of consecutive primes
`p_p · p_{p+1} ⋯ p_{q−1}` (`Nat.nth Nat.Prime` indexed from `0`). -/
def IsConsecutivePrimeProduct (m : ℕ) : Prop :=
  ∃ p q : ℕ, m = ∏ i ∈ Finset.Ico p q, nth Nat.Prime i

/-- The fifth prime (`0`-indexed) is `13`. -/
theorem nth_prime_five_eq_thirteen : nth Nat.Prime 5 = 13 := by
  have h : Nat.count Nat.Prime 13 = 5 := by decide
  rw [← h]
  exact Nat.nth_count (by decide)

/-- The sixth prime (`0`-indexed) is `17`. -/
theorem nth_prime_six_eq_seventeen : nth Nat.Prime 6 = 17 := by
  have h : Nat.count Nat.Prime 17 = 6 := by decide
  rw [← h]
  exact Nat.nth_count (by decide)

/-- `p_0 · p_1 = 2 · 3 = 6`. -/
theorem prod_Ico_zero_two : ∏ i ∈ Finset.Ico 0 2, nth Nat.Prime i = 6 := by
  rw [show Finset.Ico 0 2 = ({0, 1} : Finset ℕ) from by decide]
  norm_num [Finset.prod_insert, nth_prime_zero_eq_two, nth_prime_one_eq_three]

/-- `p_0 ⋯ p_3 = 2 · 3 · 5 · 7 = 210`. -/
theorem prod_Ico_zero_four : ∏ i ∈ Finset.Ico 0 4, nth Nat.Prime i = 210 := by
  rw [show Finset.Ico 0 4 = ({0, 1, 2, 3} : Finset ℕ) from by decide]
  norm_num [Finset.prod_insert, nth_prime_zero_eq_two, nth_prime_one_eq_three,
    nth_prime_two_eq_five, nth_prime_three_eq_seven]

/-- `p_1 · p_2 = 3 · 5 = 15`. -/
theorem prod_Ico_one_three : ∏ i ∈ Finset.Ico 1 3, nth Nat.Prime i = 15 := by
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) from by decide]
  norm_num [Finset.prod_insert, nth_prime_one_eq_three, nth_prime_two_eq_five]

/-- `p_1 · p_2 · p_3 = 3 · 5 · 7 = 105`. -/
theorem prod_Ico_one_four : ∏ i ∈ Finset.Ico 1 4, nth Nat.Prime i = 105 := by
  rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) from by decide]
  norm_num [Finset.prod_insert, nth_prime_one_eq_three, nth_prime_two_eq_five,
    nth_prime_three_eq_seven]

/-- `p_1 ⋯ p_6 = 3 · 5 · 7 · 11 · 13 · 17 = 255255`. -/
theorem prod_Ico_one_seven : ∏ i ∈ Finset.Ico 1 7, nth Nat.Prime i = 255255 := by
  rw [show Finset.Ico 1 7 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) from by decide]
  norm_num [Finset.prod_insert, nth_prime_one_eq_three, nth_prime_two_eq_five,
    nth_prime_three_eq_seven, nth_prime_four_eq_eleven, nth_prime_five_eq_thirteen,
    nth_prime_six_eq_seventeen]

/-- `p_2 · p_3 = 5 · 7 = 35`. -/
theorem prod_Ico_two_four : ∏ i ∈ Finset.Ico 2 4, nth Nat.Prime i = 35 := by
  rw [show Finset.Ico 2 4 = ({2, 3} : Finset ℕ) from by decide]
  norm_num [Finset.prod_insert, nth_prime_two_eq_five, nth_prime_three_eq_seven]

/-- `p_2 · p_3 · p_4 · p_5 = 5 · 7 · 11 · 13 = 5005`. -/
theorem prod_Ico_two_six : ∏ i ∈ Finset.Ico 2 6, nth Nat.Prime i = 5005 := by
  rw [show Finset.Ico 2 6 = ({2, 3, 4, 5} : Finset ℕ) from by decide]
  norm_num [Finset.prod_insert, nth_prime_two_eq_five, nth_prime_three_eq_seven,
    nth_prime_four_eq_eleven, nth_prime_five_eq_thirteen]

/-- `p_3 · p_4 · p_5 = 7 · 11 · 13 = 1001`. -/
theorem prod_Ico_three_six : ∏ i ∈ Finset.Ico 3 6, nth Nat.Prime i = 1001 := by
  rw [show Finset.Ico 3 6 = ({3, 4, 5} : Finset ℕ) from by decide]
  norm_num [Finset.prod_insert, nth_prime_three_eq_seven, nth_prime_four_eq_eleven,
    nth_prime_five_eq_thirteen]

/-- The numerical identities on the page. -/
theorem weisenberg_values :
    (7).choose 3 = 5 * 7 ∧ (10).choose 4 = 2 * 3 * 5 * 7 ∧ (14).choose 4 = 7 * 11 * 13 ∧
      (15).choose 6 = 5 * 7 * 11 * 13 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Weisenberg's four examples with `3 ≤ k ≤ n − 3`. -/
theorem weisenberg_examples :
    IsConsecutivePrimeProduct ((7).choose 3) ∧ IsConsecutivePrimeProduct ((10).choose 4) ∧
      IsConsecutivePrimeProduct ((14).choose 4) ∧ IsConsecutivePrimeProduct ((15).choose 6) := by
  refine ⟨⟨2, 4, ?_⟩, ⟨0, 4, ?_⟩, ⟨3, 6, ?_⟩, ⟨2, 6, ?_⟩⟩
  · rw [prod_Ico_two_four]; decide
  · rw [prod_Ico_zero_four]; decide
  · rw [prod_Ico_three_six]; decide
  · rw [prod_Ico_two_six]; decide

/-- Hence Erdős–Graham's "probably this can never happen for `3 ≤ k ≤ n − 3`" fails. -/
theorem exists_middle_consecutivePrimeProduct :
    ∃ n k : ℕ, 3 ≤ k ∧ k ≤ n - 3 ∧ IsConsecutivePrimeProduct (n.choose k) := by
  exact ⟨7, 3, by norm_num, by norm_num, weisenberg_examples.1⟩

/-- The known values `n = 4, 6, 15, 21, 715` for which `C(n, 2)` is a product of consecutive
primes (`6 = 2·3`, `15 = 3·5`, `105 = 3·5·7`, `210 = 2·3·5·7`, `255255 = 3·5·7·11·13·17`). -/
theorem choose_two_examples :
    ∀ n ∈ ({4, 6, 15, 21, 715} : Finset ℕ), IsConsecutivePrimeProduct (n.choose 2) := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, by rw [prod_Ico_zero_two]; decide⟩
  · exact ⟨1, 3, by rw [prod_Ico_one_three]; decide⟩
  · exact ⟨1, 4, by rw [prod_Ico_one_four]; decide⟩
  · exact ⟨0, 4, by rw [prod_Ico_zero_four]; decide⟩
  · exact ⟨1, 7, by rw [prod_Ico_one_seven, Nat.choose_two_right]⟩

end Erdos386

/-- **Erdős #386, the page's examples, closed form**: Weisenberg's four binomial coefficients with
`3 ≤ k ≤ n − 3` and `C(n, 2)` for `n ∈ {4, 6, 15, 21, 715}` are products of consecutive primes. -/
theorem erdos_386_examples_closed :
    (∃ p q : ℕ, (7).choose 3 = ∏ i ∈ Finset.Ico p q, Nat.nth Nat.Prime i) ∧
      (∃ p q : ℕ, (10).choose 4 = ∏ i ∈ Finset.Ico p q, Nat.nth Nat.Prime i) ∧
      (∃ p q : ℕ, (14).choose 4 = ∏ i ∈ Finset.Ico p q, Nat.nth Nat.Prime i) ∧
      (∃ p q : ℕ, (15).choose 6 = ∏ i ∈ Finset.Ico p q, Nat.nth Nat.Prime i) ∧
      ∀ n ∈ ({4, 6, 15, 21, 715} : Finset ℕ),
        ∃ p q : ℕ, n.choose 2 = ∏ i ∈ Finset.Ico p q, Nat.nth Nat.Prime i := by
  exact ⟨Erdos386.weisenberg_examples.1, Erdos386.weisenberg_examples.2.1,
    Erdos386.weisenberg_examples.2.2.1, Erdos386.weisenberg_examples.2.2.2,
    Erdos386.choose_two_examples⟩
