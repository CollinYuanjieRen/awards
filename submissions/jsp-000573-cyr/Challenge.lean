/- leanprover/lean4:v4.34.0-rc1  mathlib 1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d -/
/-
Comparator challenge for the JSP-000573 submission (Erdős Problem 703, exact value of `T(n, r)`
for large `n`, Frankl–Füredi 1984 Theorem 1.3).  This module contains only statements proved by
`sorry` and imports only Mathlib, in the format of leanprover/comparator challenge modules.  The
definitions `Erdos703.AvoidsRIntersection` and `Erdos703.T` (together with the surrounding
`noncomputable section` and the local `Classical.propDecidable` instance) are copied verbatim from
plby/lean-proofs `src/latest/ErdosProblems/Erdos703.lean` (commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e); `FranklFuredi.ffBound` is copied verbatim from
`JSP573/FF/Counting.lean`.  The solution module is `JSP573.FF.Main`.
-/

import Mathlib

namespace Erdos703

open Nat Finset Real
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- No two members of `𝓕`, including a member paired with itself, meet in `r` points. -/
def AvoidsRIntersection (r : ℕ) (𝓕 : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, #(A ∩ B) ≠ r

/-- The extremal quantity in Erdős Problem 703. -/
def T (n r : ℕ) : ℕ :=
  (((range n).powerset.powerset).filter (AvoidsRIntersection r)).sup card

end

end Erdos703

namespace FranklFuredi

open Finset

/-- The closed form of `#𝓕*(n, t)`: sets of size `< t`, sets of size `> (n + t) / 2`, and, when
`n + t` is even, the sets of size `(n + t) / 2` avoiding the fixed element `0`. -/
def ffBound (n t : ℕ) : ℕ :=
  (∑ i ∈ Finset.range t, n.choose i) + (∑ i ∈ Finset.Ioc ((n + t) / 2) n, n.choose i) +
    (if (n + t) % 2 = 0 then (n - 1).choose ((n + t) / 2) else 0)

/-- Theorem 1.3 (Frankl–Füredi 1984): for every `t ≥ 1` and all sufficiently large `n`,
`T(n, t) = #𝓕*(n, t) = ffBound n t`. -/
theorem frankl_furedi (t : ℕ) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Erdos703.T n t = ffBound n t := by
  sorry

/-- Together with `T(n, 0) = 2 ^ (n - 1)` (Erdős's trivial case, plby), the exact value is known
for every `r` and all large `n`. -/
theorem erdos_703_exact (r : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Erdos703.T n r = if r = 0 then 2 ^ (n - 1) else ffBound n r := by
  sorry

end FranklFuredi
