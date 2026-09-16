import Mathlib

/-!
# Erdős Problem 494: definitions

`sumMultiset` and `Erdos494Unique` are reproduced verbatim from
google-deepmind/formal-conjectures `FormalConjectures/ErdosProblems/494.lean` (Apache 2.0), so
that the theorems proved here are stated for exactly the objects of the comparator statements
`erdos_494.variants.card_divisible_by_prime_gt_k` and `erdos_494.variants.k_eq_2_card_not_pow_two`.

We also fix the power sums `psum A j = ∑ a ∈ A, a ^ j`, the power sums `sigma A s j` of the
multiset of `s`-fold sums, and the integer coefficients
`acoef n j m = ∑_{c=1}^{m} (-1)^(c-1) c^(j-1) C(n, m-c)` that govern the Selfridge–Straus
recursion (the coefficient of `S_j` in `j! · coeff_j e_m`).
-/

open Finset

namespace Erdos494

/--
For a finite set $A \subset \mathbb{C}$ and $k \ge 1$, define $A_k$ as the multiset consisting of
all sums of $k$ distinct elements of $A$.
-/
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

/-- The `j`-th power sum `S_j(A) = ∑_{a ∈ A} a^j`. -/
def psum (A : Finset ℂ) (j : ℕ) : ℂ := ∑ a ∈ A, a ^ j

/-- The `j`-th power sum of the `s`-fold sums of distinct elements of `A`. -/
def sigma (A : Finset ℂ) (s j : ℕ) : ℂ := ∑ T ∈ A.powersetCard s, (∑ a ∈ T, a) ^ j

/-- Equal multisets of `s`-fold sums have equal power sums. -/
theorem sigma_eq_of_sumMultiset_eq {A B : Finset ℂ} {s : ℕ}
    (h : sumMultiset A s = sumMultiset B s) (j : ℕ) : sigma A s j = sigma B s j := by
  have key : ∀ C : Finset ℂ, sigma C s j = ((sumMultiset C s).map (· ^ j)).sum := by
    intro C
    rw [sumMultiset, Multiset.map_map]
    rfl
  rw [key A, key B, h]

/-- The Selfridge–Straus coefficient: `acoef n j m = ∑_{c=1}^{m} (-1)^(c-1) c^(j-1) C(n, m-c)`.
It is the coefficient of `S_j(A)` in `j! · coeff_j (e_m)` for a set `A` of size `n`
(see `Coeff.lean`); e.g. `acoef n j 2 = n - 2^(j-1)`. -/
def acoef (n j m : ℕ) : ℤ :=
  ∑ c ∈ Finset.Icc 1 m, (-1) ^ (c - 1) * (c : ℤ) ^ (j - 1) * (n.choose (m - c) : ℤ)

end Erdos494
