import Mathlib

/-!
# Erdős Problem #820: the values `H(n)` for `1 ≤ n ≤ 10`

Erdős defines `H(n)` as the smallest integer `l` such that there exists `k < l` with
`gcd(k^n − 1, l^n − 1) = 1`, and asks whether `H(n) = 3` infinitely often and for the growth of
`H(n)` (OPEN; not addressed here).  The problem page records "The sequence `H(n)` for
`1 ≤ n ≤ 10` is `3, 3, 3, 6, 3, 18, 3, 6, 3, 12`."  This file verifies these ten values.

Definition.  As on the page, `k` ranges over integers with `2 ≤ k < l` (with `k = 1` allowed one
would have `gcd(0, l^n − 1) = l^n − 1`, which equals `1` only for `l = 2, n = 1`, giving
`H(1) = 2` instead of the page's `3`); `H n = sInf {l | ∃ k < l, 2 ≤ k ∧ Nat.Coprime (k^n − 1) (l^n − 1)}`
(the bounded-quantifier spelling makes the predicate decidable).  For `n ≥ 1` the set is nonempty (`k = 2, l = 3` works whenever
`gcd(2^n − 1, 3^n − 1) = 1`, and in general some `l` exists — but only the ten listed values are
claimed).  There is no formal-conjectures rendering of this problem; the definition is ours.  All
verifications are kernel-checked computations (`decide` with Mathlib's `Nat.gcd`), not
`native_decide`.
-/

namespace Erdos820

/-- The defining property of a candidate value `l` for `H(n)`: some `2 ≤ k < l` has
`gcd(k^n − 1, l^n − 1) = 1`. -/
def Good (n l : ℕ) : Prop := ∃ k < l, 2 ≤ k ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1)

/-- `H n` is the least `l` with `Good n l`. -/
noncomputable def H (n : ℕ) : ℕ := sInf {l | Good n l}

/-- `Good n l` is decidable (bounded search over `k`). -/
instance (n l : ℕ) : Decidable (Good n l) := by
  unfold Good; infer_instance

/-- If `m` is the least good value then `H n = m`. -/
theorem H_eq_of_isLeast {n m : ℕ} (h : IsLeast {l | Good n l} m) : H n = m :=
  h.csInf_eq

/-- If `m` is good and no `l < m` is good, then `H n = m`. -/
theorem H_eq_of_good_of_forall_lt {n m : ℕ} (h1 : Good n m) (h2 : ∀ l < m, ¬ Good n l) :
    H n = m :=
  H_eq_of_isLeast ⟨h1, fun l hl => not_lt.mp fun h => h2 l h hl⟩

/-- The page's table: `H(1), …, H(10) = 3, 3, 3, 6, 3, 18, 3, 6, 3, 12`. -/
theorem H_table :
    H 1 = 3 ∧ H 2 = 3 ∧ H 3 = 3 ∧ H 4 = 6 ∧ H 5 = 3 ∧ H 6 = 18 ∧ H 7 = 3 ∧ H 8 = 6 ∧ H 9 = 3 ∧
      H 10 = 12 := by
  exact ⟨H_eq_of_good_of_forall_lt (by decide) (by decide),
    H_eq_of_good_of_forall_lt (by decide) (by decide),
    H_eq_of_good_of_forall_lt (by decide) (by decide),
    H_eq_of_good_of_forall_lt (by decide) (by decide),
    H_eq_of_good_of_forall_lt (by decide) (by decide),
    H_eq_of_good_of_forall_lt (by decide) (by decide),
    H_eq_of_good_of_forall_lt (by decide) (by decide),
    H_eq_of_good_of_forall_lt (by decide) (by decide),
    H_eq_of_good_of_forall_lt (by decide) (by decide),
    H_eq_of_good_of_forall_lt (by decide) (by decide)⟩

end Erdos820

open Erdos820 in
/-- **Erdős #820, the page's table, closed form**: `H(n)` for `n = 1, …, 10` equals
`3, 3, 3, 6, 3, 18, 3, 6, 3, 12`. -/
theorem erdos_820_table_closed :
    H 1 = 3 ∧ H 2 = 3 ∧ H 3 = 3 ∧ H 4 = 6 ∧ H 5 = 3 ∧ H 6 = 18 ∧ H 7 = 3 ∧ H 8 = 6 ∧ H 9 = 3 ∧
      H 10 = 12 := by
  exact Erdos820.H_table
