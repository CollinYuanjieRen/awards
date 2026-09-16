# JSP-000185: every permutation of ℕ contains a monotone 3-term arithmetic progression (Erdős #196, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000185](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000185) / [Erdős Problem #196](https://www.erdosproblems.com/196): must every permutation `x` of `ℕ` contain a monotone 4-term arithmetic progression, i.e. indices `i < j < k < l` (or `i > j > k > l`) with `x_i, x_j, x_k, x_l` in arithmetic progression? The component formalized here is the positive result of Davis, Entringer, Graham and Simmons (1977) recorded on the problem page: **every permutation of `ℕ` contains a monotone 3-term arithmetic progression** (indeed an increasing one). The 4-term question itself (the catalog question; a negative construction with a Lean file was reported in the problem page's proof-claims thread in September 2026 and is pending review) and the DEGS77 construction of a permutation without monotone 5-term progressions are **not** claimed. This is the known positive half and is labelled as such.

## Statements

All definitions are our own (namespace `Erdos196`, [Proof/Main.lean](Proof/Main.lean)); a permutation of `ℕ` is `x : ℕ ≃ ℕ`:

```lean
def HasMonotoneAP3 (x : ℕ ≃ ℕ) : Prop := ∃ i j k : ℕ, i < j ∧ j < k ∧ x i + x k = 2 * x j

def HasIncreasingAP3 (x : ℕ ≃ ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧ x i < x j ∧ x j < x k ∧ x i + x k = 2 * x j

theorem exists_monotoneAP3 (x : ℕ ≃ ℕ) : HasMonotoneAP3 x

theorem exists_increasingAP3 (x : ℕ ≃ ℕ) : HasIncreasingAP3 x
```

`HasMonotoneAP3` is the page's notion for three terms: increasing indices whose values form an arithmetic progression (the reversed index order `i > j > k` describes the same triples). The first theorem is the DEGS77 statement; the second is the stronger form actually proved, in which the progression is increasing. There are no hypotheses, no custom axioms and no unproved inputs.

## Proof outline

Let `m = x 0` and let `p = x⁻¹` give positions. For `d ≥ 1` the values `m + d` and `m + 2d` occur at positions `p(m + d)` and `p(m + 2d)`, both nonzero. If `p(m + d) < p(m + 2d)` for some `d ≥ 1`, the indices `0 < p(m + d) < p(m + 2d)` carry the increasing progression `m, m + d, m + 2d`. Otherwise `p(m + 2d) < p(m + d)` for every `d ≥ 1`, so `p(m + 2^(j+1)) < p(m + 2^j)` for all `j`: an infinite strictly decreasing sequence of natural numbers, which is impossible.

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

The problem is due to Erdős and Graham; the 3-term theorem is due to J. A. Davis, R. C. Entringer, R. L. Graham and G. J. Simmons, *On permutations containing no long arithmetic progressions*, Acta Arithmetica 34 (1977/78), 81–90. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the 4-term question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000185-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
