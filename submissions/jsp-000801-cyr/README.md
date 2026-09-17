# JSP-000801: the greedy bound f(n) ≥ ⌊log₃ n⌋ for dissociated subsets (Erdős #963, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000801](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000801) / [Erdős Problem #963](https://www.erdosproblems.com/963): with `f(n)` the largest `k` such that every `n`-element set `A ⊂ ℝ` contains a dissociated subset `B` (all subset sums distinct) of size at least `k`, estimate `f(n)`; in particular is `f(n) ≥ ⌊log₂ n⌋`? The component formalized here is the bound recorded on the problem page, **"Erdős noted that the greedy algorithm showed `f(n) ≥ ⌊log₃ n⌋`"**: a dissociated subset `B ⊆ A` of maximal size represents every element of `A` as a `{−1, 0, 1}`-combination of `B`, injectively, so `|A| ≤ 3^{|B|}`. The `⌊log₂ n⌋` question and any better bound are **not** claimed.

## Statements

Finite sets of reals are Mathlib `Finset ℝ`; the dissociation predicate and `f` are defined in this package; `Nat.log 3 n` is `⌊log₃ n⌋` (namespace `Erdos963`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def Dissociated (B : Finset ℝ) : Prop := ∀ S ⊆ B, ∀ T ⊆ B, ∑ x ∈ S, x = ∑ x ∈ T, x → S = T

noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n → ∃ B ⊆ A, Dissociated B ∧ k ≤ B.card}

theorem log_three_le_f (n : ℕ) : Nat.log 3 n ≤ f n

theorem exists_dissociated_subset (A : Finset ℝ) : ∃ B ⊆ A, Dissociated B ∧ A.card ≤ 3 ^ B.card

theorem exists_dissociated_subset_log (A : Finset ℝ) :
    ∃ B ⊆ A, Dissociated B ∧ Nat.log 3 A.card ≤ B.card

theorem f_le (n : ℕ) : f n ≤ n

theorem exists_dissociated_subset_f (n : ℕ) (A : Finset ℝ) (hA : A.card = n) :
    ∃ B ⊆ A, Dissociated B ∧ f n ≤ B.card
```

`f n` is the page's `f(n)`. The first theorem (data binder `n`) is Erdős's greedy bound; the second is the per-set statement `|A| ≤ 3^{|B|}` that drives it, and the third its logarithmic form; the last two make `f` transparent (`f(n) ≤ n`, and every `n`-set contains a dissociated subset of size `≥ f(n)`). There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Let `B ⊆ A` be dissociated of maximal size. For `a ∈ A ∖ B`, `B ∪ {a}` is not dissociated, so two distinct subsets have equal sums; `a` lies in exactly one of them (otherwise `B` itself would fail), and cancelling the common part writes `a = Σ_{T} b − Σ_{S} b` with disjoint `S, T ⊆ B`. Assigning to each `a ∈ A` the vector `ε_a ∈ {−1, 0, 1}^B` with `a = Σ_b ε_a(b) b` (the indicator of `{a}` for `a ∈ B`) is injective, so `|A| ≤ 3^{|B|}`, i.e. `⌊log₃ |A|⌋ ≤ |B|`. Hence `⌊log₃ n⌋` lies in the set defining `f(n)`, whose elements are at most `n`, and `f(n) ≥ ⌊log₃ n⌋`.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's (Er65; Va99, 1.22). The greedy bound is Erdős's observation, as recorded on the problem page. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000801-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
