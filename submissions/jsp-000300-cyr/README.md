# JSP-000300: infinitely many pairs of consecutive powerful numbers (Erdős #364, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000300](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000300) / [Erdős Problem #364](https://www.erdosproblems.com/364): are there three consecutive positive integers all of which are powerful (every prime factor divides them at least twice)? The component formalized here is the observation recorded on the problem page, **Mahler's remark that there are infinitely many pairs of consecutive powerful numbers, from the infinitely many solutions of the Pell equation `x² = 8y² + 1`** (`n = 8y²` and `n + 1 = x²` are both powerful), together with the page's trivial remark that **there are no four consecutive powerful numbers** (one of them is `2 mod 4`). The open question about triples is **not** claimed.

## Statements

The predicate `Powerful` transcribes the page's definition; Mathlib's Pell development (`Pell.xn`, `Pell.yn` with `a = 3`, `d = 8`) is used inside the proofs only (namespace `Erdos364`, [Proof/Main.lean](Proof/Main.lean)):

```lean
def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

theorem exists_consecutive_powerful_gt (N : ℕ) : ∃ n : ℕ, N < n ∧ Powerful n ∧ Powerful (n + 1)

theorem infinite_consecutive_powerful : {n : ℕ | Powerful n ∧ Powerful (n + 1)}.Infinite

theorem exists_pell_gt (N : ℕ) : ∃ x y : ℕ, N < y ∧ x ^ 2 = 8 * y ^ 2 + 1

theorem powerful_eight_mul_sq (y : ℕ) : Powerful (8 * y ^ 2)

theorem powerful_sq (x : ℕ) : Powerful (x ^ 2)

theorem not_four_consecutive_powerful (n : ℕ) :
    ¬ (Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) ∧ Powerful (n + 3))
```

The first theorem (data binder `N`) says that beyond every bound there is a pair of consecutive powerful numbers; the second is the same statement as the infinitude of the set of such `n`; the third is the Pell input (solutions with `y` arbitrarily large); the fourth and fifth are the two powerfulness facts behind the pair; the sixth is the page's no-quadruples remark (the same fact is also proved in the formal-conjectures project; the proof here is our own). There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

The Pell equation `x² − 8y² = 1` has infinitely many solutions with strictly increasing `y` (Mathlib's `Pell.pell_eq` and `Pell.strictMono_y` for `a = 3`). For such a solution put `n = 8y²`: a prime dividing `n` is `2`, and `4 ∣ 8 ∣ n`, or is odd, hence divides `y` and its square divides `y² ∣ n`; and `n + 1 = x²` is a square, hence powerful. Choosing the solution with `y > N` gives `n > N`. Among four consecutive integers one is `2 mod 4`, divisible by `2` but not by `4`, hence not powerful.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definition and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definition and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's; the pairs observation is Mahler's, as recorded on the problem page, and its Pell input is taken from Mathlib. The no-quadruples remark is folklore. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000300-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
