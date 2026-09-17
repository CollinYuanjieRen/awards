import Jsp731.Coverage
import Jsp731.ExactOrder
import Jsp731.UnboundedGaps
import Jsp731.Enumeration
import Jsp731.Infinite

/-!
# JSP-000731 / Erdős #880 — the answer to the Burr–Erdős question

Erdős (1998), for Burr and himself: if `A` is an asymptotic basis of order `k` (every large
integer is a sum of `k` or fewer elements of `A`) and `b₁ < b₂ < ⋯` enumerates the integers that
are sums of `k` or fewer *distinct* elements of `A`, must `b_{i+1} − b_i` be bounded?

Hegyvári, Hennecart and Plagne (2007, Theorem 1) answered: **yes for `k = 2`** (the gaps are
eventually at most `2`) and **no for every `k ≥ 3`**.  This file assembles both halves from
`OrderTwo.lean` (the `k = 2` argument), `Construction.lean`/`Coverage.lean`/`ExactOrder.lean`/
`UnboundedGaps.lean` (the explicit basis of exact order `k` with unbounded restricted gaps) and
`Enumeration.lean` (the translation to the literal `b_{i+1} − b_i` formulation).
-/

open Filter

namespace Erdos880

/-- For every `k ≥ 3` there is a set of positive integers which is an asymptotic basis of order
exactly `k` and whose set of sums of `k` or fewer distinct elements has unbounded gaps. -/
theorem counterexample (k : ℕ) (hk : 3 ≤ k) :
    ∃ A : Set ℕ, A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧ IsAsymptoticBasis A k ∧
      (∀ j < k, ¬ IsAsymptoticBasis A j) ∧
      (distinctSums A k).Infinite ∧ ¬ HasBoundedGaps (distinctSums A k) :=
  ⟨basis k, basis_infinite hk, basis_pos hk, basis_isAsymptoticBasis hk,
    fun _ hj => not_isAsymptoticBasis_of_lt hk hj, distinctSums_basis_infinite hk,
    basis_not_hasBoundedGaps hk⟩

/-- **Erdős #880 (Burr–Erdős), resolved by Hegyvári–Hennecart–Plagne.**  The distinct-element
sumset of an asymptotic basis of order `2` has bounded gaps; for every order `k ≥ 3` this fails,
even for bases of exact order `k` consisting of positive integers. -/
theorem erdos_880 :
    (∀ A : Set ℕ, IsAsymptoticBasis A 2 → HasBoundedGaps (distinctSums A 2)) ∧
    (∀ k : ℕ, 3 ≤ k → ∃ A : Set ℕ, A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧ IsAsymptoticBasis A k ∧
      (∀ j < k, ¬ IsAsymptoticBasis A j) ∧
      (distinctSums A k).Infinite ∧ ¬ HasBoundedGaps (distinctSums A k)) :=
  ⟨order_two_bounded_gaps, counterexample⟩

/-- Literal enumeration form, with `b i := Nat.nth (· ∈ distinctSums A k) i`: for order `2` the
consecutive differences are bounded; for every order `k ≥ 3` some basis of exact order `k` has
unbounded consecutive differences. -/
theorem erdos_880_enumeration :
    (∀ A : Set ℕ, IsAsymptoticBasis A 2 → (distinctSums A 2).Infinite ∧
      ∃ C : ℕ, ∀ i : ℕ,
        Nat.nth (· ∈ distinctSums A 2) (i + 1) - Nat.nth (· ∈ distinctSums A 2) i ≤ C) ∧
    (∀ k : ℕ, 3 ≤ k → ∃ A : Set ℕ, A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧ IsAsymptoticBasis A k ∧
      (∀ j < k, ¬ IsAsymptoticBasis A j) ∧ (distinctSums A k).Infinite ∧
      ∀ C : ℕ, ∃ i : ℕ,
        C < Nat.nth (· ∈ distinctSums A k) (i + 1) - Nat.nth (· ∈ distinctSums A k) i) := by
  refine ⟨fun A hA => ⟨distinctSums_two_infinite A hA, ?_⟩, fun k hk => ?_⟩
  · exact exists_nth_diff_le_of_hasBoundedGaps (distinctSums_two_infinite A hA)
      (order_two_bounded_gaps A hA)
  · refine ⟨basis k, basis_infinite hk, basis_pos hk, basis_isAsymptoticBasis hk,
      fun _ hj => not_isAsymptoticBasis_of_lt hk hj, distinctSums_basis_infinite hk,
      fun C => ?_⟩
    exact exists_nth_diff_gt_of_not_hasBoundedGaps (distinctSums_basis_infinite hk)
      (basis_not_hasBoundedGaps hk) C

/-! ### The "exactly `k` summands" reading

Hegyvári–Hennecart–Plagne state their theorem with `hA` (sums of exactly `h` elements) and
`h × A` (sums of exactly `h` distinct elements), allowing `0 ∈ A`.  Both halves transfer. -/

/-- Exact-count counterexample: `insert 0 (basis k)`. -/
theorem exact_counterexample (k : ℕ) (hk : 3 ≤ k) :
    ∃ A : Set ℕ, A.Infinite ∧ (∀ᶠ n in atTop, IsSumOfExactly A k n) ∧
      (∀ j < k, ¬ ∀ᶠ n in atTop, IsSumOfExactly A j n) ∧
      (exactDistinctSums A k).Infinite ∧ ¬ HasBoundedGaps (exactDistinctSums A k) := by
  refine ⟨insert 0 (basis k), (basis_infinite hk).mono (Set.subset_insert _ _), ?_,
    fun j hj hev => ?_, exactDistinctSums_insert_zero_basis_infinite hk, fun hb => ?_⟩
  · exact (basis_isAsymptoticBasis hk).mono fun n hn => isSumOfExactly_insert_zero hn
  · exact not_isAsymptoticBasis_of_lt hk hj
      (hev.mono fun n hn => isSumOfAtMost_of_exactly_insert_zero hn)
  · exact basis_not_hasBoundedGaps hk
      (hasBoundedGaps_mono (exactDistinctSums_insert_zero_subset _ _) hb)

/-- Erdős #880 in the exact-count reading. -/
theorem erdos_880_exact :
    (∀ A : Set ℕ, (∀ᶠ n in atTop, IsSumOfExactly A 2 n) →
      HasBoundedGaps (exactDistinctSums A 2)) ∧
    (∀ k : ℕ, 3 ≤ k → ∃ A : Set ℕ, A.Infinite ∧ (∀ᶠ n in atTop, IsSumOfExactly A k n) ∧
      (∀ j < k, ¬ ∀ᶠ n in atTop, IsSumOfExactly A j n) ∧
      (exactDistinctSums A k).Infinite ∧ ¬ HasBoundedGaps (exactDistinctSums A k)) :=
  ⟨exact_order_two_bounded_gaps, exact_counterexample⟩

end Erdos880
