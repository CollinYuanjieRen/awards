# JSP-000308: Erdős #373, the trivial solutions of `n! = a₁! ⋯ a_k!` and Hickerson's four solutions

This package submits, for intake and eligibility review, Lean proofs of two remarks recorded on the page of [JSP-000308](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000308) / [Erdős Problem #373](https://www.erdosproblems.com/373): show that `n! = a₁! a₂! ⋯ a_k!` with `n − 1 > a₁ ≥ a₂ ≥ ⋯ ≥ a_k ≥ 2` has only finitely many solutions.

**Scope statement.** The finiteness question is open and is not addressed, nor are Luca's conditional result, the `k = 2` bounds, or Hickerson's conjecture that the four solutions below are the only ones. The problem page records: "The condition `a₁ < n − 1` is necessary to rule out the trivial solutions when `n = a₂! ⋯ a_k!`", and that Hickerson conjectured that the only non-trivial solutions are `9! = 2!3!3!7!`, `10! = 6!7!`, `10! = 3!5!7!` and `16! = 14!5!2!`. With the set `S` of non-trivial solutions copied verbatim from the formal-conjectures statement `Erdos373.erdos_373` (pairs `(n, l)`, `l = [a₁, …, a_k]` non-increasing), this package proves that the trivial tuples `(n, [n − 1, a₂, …, a_k])` with `n = a₂! ⋯ a_k!` satisfy the equation, the ordering and `a_i ≥ 2` but are excluded from `S` by `a₁ < n − 1`, and that Hickerson's four solutions are elements of `S`.

## Statement and proof

[Erdos373Solutions/Main.lean](Erdos373Solutions/Main.lean) proves

```lean
theorem erdos_373_trivial_solution (l : List ℕ) (hl0 : l ≠ []) (hl : l.Pairwise (· ≥ ·))
    (h2 : ∀ a ∈ l, 1 < a) (hn : l.headI + 1 ≤ (l.map Nat.factorial).prod) :
    ((l.map Nat.factorial).prod) ! = ((((l.map Nat.factorial).prod - 1) :: l).map Nat.factorial).prod ∧
      (((l.map Nat.factorial).prod - 1) :: l).Pairwise (· ≥ ·) ∧
      ∀ a ∈ ((l.map Nat.factorial).prod - 1) :: l, 1 < a

theorem erdos_373_trivial_solution_not_mem (l : List ℕ) :
    ((l.map Nat.factorial).prod, ((l.map Nat.factorial).prod - 1) :: l) ∉ S

theorem erdos_373_hickerson_mem :
    (9, [7, 3, 3, 2]) ∈ S ∧ (10, [7, 6]) ∈ S ∧ (10, [7, 5, 3]) ∈ S ∧ (16, [14, 5, 2]) ∈ S
```

and the closed conjunction `erdos_373_remarks_closed` of all of these. Here `l = [a₂, …, a_k]` is nonempty (`k ≥ 2`, as in `n = a₂! ⋯ a_k!`) and the hypothesis `a₂ + 1 ≤ n` is the ordering requirement `a₁ = n − 1 ≥ a₂` (it fails only for the degenerate `n = 2! = 2`).

Proof. `n! = (n − 1)! · n` with `n = a₂! ⋯ a_k!` gives the equation; the ordering and the bounds follow from `n − 1 ≥ a₂` and `a_i ≥ 2`; the head of the trivial tuple equals `n − 1`, so `a₁ < n − 1` fails and the tuple is not in `S`. The four memberships are decided by the kernel by evaluating the factorials.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the memberships as a typed `example`, checks by `rfl` that `S` is the formal-conjectures set, and prints the axioms (a subset of the standard `propext`, `Classical.choice`, `Quot.sound`; see [verification.txt](verification.txt) for the exact lists). The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the axioms used are stated explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
