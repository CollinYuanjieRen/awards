import Mathlib

/-!
# JSP-000751 / Erdős #903 — definitions

Erdős–Sós [Er82e]: let `n = p² + p + 1` and let `A_1, …, A_t ⊆ {1, …, n}` be a block design
(every pair of distinct points lies in exactly one `A_i`).  Is it true that if `t > n` then
`t ≥ n + p`?  Proved by Erdős, Fowler, Sós and Wilson [EFSW85, Theorem 2], for every `p`.

A *block design* here is a pairwise balanced design of index one, also called a linear space:
the blocks have at least two points (the standard convention, and the definition used in
[EFSW85]; without it empty blocks could be added freely and the question would be false) and
every pair of distinct points lies in exactly one block.  Points are `Fin v`, blocks are indexed
by `Fin b` (repeated blocks are impossible, since two equal blocks would cover a pair twice).
-/

open Finset

namespace Erdos903

/-- A pairwise balanced design of index one (linear space) on `Fin v` with `b` indexed blocks:
every block has at least two points, and every pair of distinct points lies in exactly one
block. -/
def IsLinearSpace {v b : ℕ} (block : Fin b → Finset (Fin v)) : Prop :=
  (∀ i, 2 ≤ #(block i)) ∧ ∀ x y : Fin v, x ≠ y → ∃! i, x ∈ block i ∧ y ∈ block i

/-- The blocks through a point. -/
def through {v b : ℕ} (block : Fin b → Finset (Fin v)) (x : Fin v) : Finset (Fin b) :=
  univ.filter fun i => x ∈ block i

/-- The degree (replication number) of a point: the number of blocks through it. -/
def degree {v b : ℕ} (block : Fin b → Finset (Fin v)) (x : Fin v) : ℕ :=
  #(through block x)

end Erdos903
