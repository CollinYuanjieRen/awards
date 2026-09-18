import Mathlib

/-!
# JSP-001010 / Erdős #1205 — definitions

Erdős [Er80, p. 108]: let `F(x)` be maximal such that there exists, for all `n ≤ x`, a congruence
class `a_n (mod n)` such that every `m ≤ x` satisfies at least `F(x)` of these congruences.
Estimate `F(x)`.

A choice of classes is a function `a : ℕ → ℕ` (only `a n mod n` matters); `m` satisfies the
`n`-th congruence when `m ≡ a n (mod n)`, i.e. `m % n = a n % n`.
-/

open Finset

namespace Erdos1205

/-- The number of moduli `n ∈ [1, x]` whose chosen class contains `m`. -/
def coverCount (a : ℕ → ℕ) (x m : ℕ) : ℕ :=
  ((Icc 1 x).filter fun n => m % n = a n % n).card

/-- `F x`: the largest `k` such that some choice of classes makes every `m ∈ [1, x]` satisfy at
least `k` of the congruences. (For `x ≥ 1` the set is nonempty and bounded by `x`, so `sSup` is its
maximum; for `x = 0` the set is all of `ℕ` and `F 0 = 0`.) -/
noncomputable def F (x : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : ℕ → ℕ, ∀ m ∈ Icc 1 x, k ≤ coverCount a x m}

/-! ### The finite probability space used for the lower bound
Moduli `1, …, N` are indexed by `i : Fin N` (modulus `i + 1`); a choice is `a : Fin N → ℕ`
with `a i < i + 1`. -/

/-- All choices of one class for each modulus `1, …, N`. -/
def choices (N : ℕ) : Finset (Fin N → ℕ) :=
  Fintype.piFinset fun i : Fin N => range (i.1 + 1)

/-- The number of moduli among `1, …, N` whose chosen class contains `m`. -/
def smallCount (N : ℕ) (a : Fin N → ℕ) (m : ℕ) : ℕ :=
  (univ.filter fun i : Fin N => m % (i.1 + 1) = a i).card

end Erdos1205
