# JSP-000251: the Erdős–Straus lower bound k(N) ≥ (e − 1)(N − 1) (Erdős #295, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000251](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000251) / [Erdős Problem #295](https://www.erdosproblems.com/295): for `N ≥ 1` let `k(N)` be the least `k` such that `1 = 1/n₁ + ⋯ + 1/n_k` with `N ≤ n₁ < ⋯ < n_k`. Erdős and Straus (1971) proved `−c < k(N) − (e − 1)N ≪ N / log N`; the problem asks whether `k(N) − (e − 1)N → ∞`, which is open. The component formalized here is the **lower half with the explicit constant**: `k(N) ≥ (e − 1)(N − 1)` for every `N`. The open question and the upper bound `k(N) − (e − 1)N ≪ N / log N` are **not** claimed.

## Statements

All definitions are our own (namespace `Erdos295`, [Proof/Defs.lean](Proof/Defs.lean)):

```lean
def IsUnitRepr (N : ℕ) (D : Finset ℕ) : Prop :=           -- distinct denominators ≥ N summing to 1
  (∀ d ∈ D, N ≤ d) ∧ ∑ d ∈ D, (1 : ℚ) / d = 1

noncomputable def kmin (N : ℕ) : ℕ :=                     -- Erdős's k(N)
  sInf {m : ℕ | ∃ D : Finset ℕ, IsUnitRepr N D ∧ D.card = m}
```

[Proof/Main.lean](Proof/Main.lean) proves:

```lean
theorem card_ge_of_isUnitRepr (N : ℕ) (D : Finset ℕ) (hD : IsUnitRepr N D) :
    (Real.exp 1 - 1) * ((N : ℝ) - 1) ≤ D.card

theorem le_kmin (N : ℕ) (h : ∃ D : Finset ℕ, IsUnitRepr N D) :
    (Real.exp 1 - 1) * ((N : ℝ) - 1) ≤ kmin N
```

The first theorem is the bound in universal form: every representation of `1` by distinct unit fractions with denominators at least `N` has at least `(e − 1)(N − 1)` terms. A `Finset ℕ` has distinct elements, so this is exactly "`N ≤ n₁ < ⋯ < n_k`". The second restates it for `k(N)`; its hypothesis is needed only because `sInf ∅ = 0` in `ℕ` (that representations exist for every `N ≥ 1` is not part of this component). There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline ([Proof/Bound.lean](Proof/Bound.lean), [Proof/Main.lean](Proof/Main.lean))

The maximum of `k` distinct naturals that are all `≥ N` is at least `N + k − 1`, so removing the maximum and inducting gives `∑_{d ∈ D} 1/d ≤ ∑_{i < k} 1/(N + i)` for `N ≥ 1`. Since `log(m + 1) − log m ≥ 1/(m + 1)` for `m ≥ 1` (from `log x ≤ x − 1`), the harmonic block satisfies `∑_{i < k} 1/(N + i) ≤ 1/N + log(N + k − 1) − log N`. If `D` represents `1` with `N ≥ 1`, then `1 ≤ 1/N + log((N + k − 1)/N)`, so `(N + k − 1)/N ≥ exp(1 − 1/N) = e · exp(−1/N) ≥ e(1 − 1/N)`, i.e. `k ≥ (e − 1)(N − 1)`. For `N = 0` the right-hand side is negative.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for both theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's; the estimate `−c < k(N) − (e − 1)N ≪ N / log N` is due to P. Erdős and E. G. Straus, American Mathematical Monthly 78 (1971), 302–303 (the lower half formalized here is the elementary logarithm comparison; the paper is paywalled and the statement is taken from the problem page). The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the open question or the upper bound. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000251-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
