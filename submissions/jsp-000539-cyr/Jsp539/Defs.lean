import Mathlib

/-!
# JSP-000539 / Erdős #664 — definitions

Erdős [Er81, Er97f]: let `c < 1` be a constant and `A_1, …, A_m ⊆ {1, …, n}` satisfy `|A_i| > c√n`
for all `i` and `|A_i ∩ A_j| ≤ 1` for all `i ≠ j`.  Must there exist some set `B` such that
`B ∩ A_i ≠ ∅` and `|B ∩ A_i| ≪_c 1` for all `i`?

The definitions below coincide with the public comparator challenge statement
(`ref/plby-Erdos664-challenge.lean`): the ground set `{1, …, n}` is `Fin n`, the family is indexed by
`Fin m`, and "`≪_c 1`" is a constant `K` depending only on `c`.
-/

open Finset

namespace Erdos664

/-- Pairwise intersections have at most one element. -/
def LinearFamily {ι α : Type*} [DecidableEq α] (A : ι → Finset α) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → #(A i ∩ A j) ≤ 1

/-- `B` meets every member of the family. -/
def HitsAll {ι α : Type*} [Fintype ι] [DecidableEq α] (A : ι → Finset α) (B : Finset α) : Prop :=
  ∀ i, (B ∩ A i).Nonempty

/-- "`K` is a uniform transversal bound for `c`": every family `A_1, …, A_m ⊆ {1, …, n}` with
`|A_i| > c√n` and pairwise intersections of size at most one has a set `B` meeting every `A_i`
in at least one and at most `K` points. -/
def HasUniformTransversalBound (c : ℝ) (K : ℕ) : Prop :=
  ∀ n m : ℕ, ∀ A : Fin m → Finset (Fin n),
    (∀ i, c * Real.sqrt n < #(A i)) →
    LinearFamily A →
    ∃ B : Finset (Fin n), HitsAll A B ∧ ∀ i, #(B ∩ A i) ≤ K

end Erdos664
