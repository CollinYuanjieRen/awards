# JSP-000901: the one-dimensional contact number f₁(n) = n − 1 (Erdős #1084, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000901](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000901) / [Erdős Problem #1084](https://www.erdosproblems.com/1084): for `n` points in `ℝ^d` with all pairwise distances at least `1`, `f_d(n)` is the least `M` such that every such set has at most `M` pairs at distance exactly `1` (equivalently the maximum number of such pairs, since the bound is attained); the problem asks for estimates of `f_d(n)`. The component formalized here is the one-dimensional value recorded on the problem page, **`f₁(n) = n − 1`**. Harborth's planar formula `f₂(n) = ⌊3n − √(12n − 3)⌋`, the three-dimensional bounds and the general-dimension estimates are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos1084`, [Proof/Defs.lean](Proof/Defs.lean)):

```lean
def IsSeparated (A : Finset ℝ) : Prop := ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|

noncomputable def unitPairs (A : Finset ℝ) : ℕ :=          -- pairs (x, x + 1) in A
  ((A ×ˢ A).filter fun p => p.2 - p.1 = 1).card

noncomputable def contactOne (n : ℕ) : ℕ :=                 -- f₁(n)
  sSup {m : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsSeparated A ∧ unitPairs A = m}
```

`unitPairs` counts ordered pairs `(x, x + 1)`, so each unordered pair of points at distance `1` is counted exactly once. [Proof/Main.lean](Proof/Main.lean) proves:

```lean
theorem contactOne_eq (n : ℕ) : contactOne n = n - 1

theorem unitPairs_le_of_isSeparated (A : Finset ℝ) (hA : IsSeparated A) :
    unitPairs A ≤ A.card - 1

theorem exists_isSeparated_unitPairs_eq (n : ℕ) :
    ∃ A : Finset ℝ, A.card = n ∧ IsSeparated A ∧ unitPairs A = n - 1
```

The first theorem is the component; the other two are its halves. The upper bound is in fact proved for every finite set of reals (`unitPairs_le` in [Proof/Defs.lean](Proof/Defs.lean)): in dimension one the separation hypothesis is not needed. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Upper bound: the map `(x, x + 1) ↦ x` from the unit pairs of `A` into `A` is injective, and its image avoids the maximum of `A` (since `x + 1 ∈ A` forces `x < max A`), so `A` has at most `|A| − 1` unit pairs. Lower bound: `{0, 1, …, n − 1}` is separated, has `n` points and exactly the `n − 1` unit pairs `(i, i + 1)`. Hence the supremum is `n − 1` (for `n = 0` both sides are `0`).

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all three theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's ([Er46b]); the one-dimensional value is the elementary observation recorded on the problem page ("it is easy to see that `f₁(n) = n − 1`"). Harborth's planar theorem (1974) and the higher-dimensional results are not formalized. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the open questions. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000901-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
