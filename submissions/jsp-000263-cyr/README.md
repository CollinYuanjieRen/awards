# JSP-000263: the non-strict inequality |Σ δₖ/k| ≥ 1/[1, …, n] for signed harmonic sums (Erdős #317, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000263](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000263) / [Erdős Problem #317](https://www.erdosproblems.com/317): is there `c > 0` such that for every `n` some signed harmonic sum `Σ_{k≤n} δₖ/k` (`δₖ ∈ {−1, 0, 1}`) satisfies `0 < |Σ δₖ/k| < c/2ⁿ`, and is it true that for sufficiently large `n` every non-zero such sum satisfies `|Σ δₖ/k| > 1/[1, …, n]`? The component formalized here is the part the page records as obvious, **"Inequality is obvious for the second claim, the problem is strict inequality"**: for every `n`, every non-zero signed harmonic sum satisfies `|Σ_{k≤n} δₖ/k| ≥ 1/[1, …, n]`, because `[1, …, n]·Σ δₖ/k` is a non-zero integer; together with the page's equality instance `1/2 − 1/3 − 1/4 = −1/12 = −1/[1, …, 4]`, which shows that strict inequality can fail. The first question, the strict inequality for sufficiently large `n` and the Kovač–van Doorn bounds are **not** claimed.

## Statements

Sums, lcm and absolute values are Mathlib's; the sign predicate and the signed sum are defined in this package, and `lcmUpTo` is reused from our JSP-000260 submission (namespace `Erdos317`, [Proof/Lcm.lean](Proof/Lcm.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def lcmUpTo (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

def IsSign (δ : ℕ → ℚ) : Prop := ∀ k, δ k = -1 ∨ δ k = 0 ∨ δ k = 1

def signedSum (n : ℕ) (δ : ℕ → ℚ) : ℚ := ∑ k ∈ Finset.Icc 1 n, δ k / k

theorem not_exists_small_signedSum (n : ℕ) :
    ¬ ∃ δ : ℕ → ℚ, IsSign δ ∧ signedSum n δ ≠ 0 ∧ |signedSum n δ| < 1 / (lcmUpTo n : ℚ)

theorem one_div_lcm_le_abs_signedSum (n : ℕ) (δ : ℕ → ℚ) (hδ : IsSign δ) (h : signedSum n δ ≠ 0) :
    1 / (lcmUpTo n : ℚ) ≤ |signedSum n δ|

theorem one_div_lcm_le_abs_fin (n : ℕ) (δ : Fin n → ℚ) (hδ : ∀ k, δ k ∈ ({-1, 0, 1} : Set ℚ))
    (h : ∑ k, δ k / (((k : ℕ) : ℚ) + 1) ≠ 0) :
    1 / (((Finset.Icc 1 n).lcm id : ℕ) : ℚ) ≤ |∑ k, δ k / (((k : ℕ) : ℚ) + 1)|

theorem exists_signedSum_eq_one_div_lcm :
    ∃ δ : ℕ → ℚ, IsSign δ ∧ signedSum 4 δ ≠ 0 ∧ |signedSum 4 δ| = 1 / (lcmUpTo 4 : ℚ)

theorem lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n
```

The first theorem (single data binder `n`, in negation form) says that no signed harmonic sum of length `n` is non-zero yet smaller than `1/[1, …, n]` in absolute value; the second is the same bound in direct form, for every `n` (the page asks only for sufficiently large `n`); the third restates it in the `Fin`-indexed encoding used by the formal-conjectures project (where the statement is left as `sorry`), so the two are comparable; the fourth is the page's equality instance at `n = 4`; the fifth is the positivity of the lcm. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Let `L = [1, …, n]`. Each `k ≤ n` divides `L`, so `L·Σ_{k≤n} δₖ/k = Σ_{k≤n} δₖ·(L/k)` is an integer, each `δₖ` being `−1`, `0` or `1` and each `L/k` a natural number. If the sum is non-zero this integer is non-zero, so its absolute value is at least `1`, and `|Σ δₖ/k| ≥ 1/L`. For `n = 4`, `L = 12` and `1/2 − 1/3 − 1/4 = −1/12`.

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

The problem is Erdős and Graham's (ErGr80, p. 42). The inequality is the folklore observation recorded on the problem page; the equality instance is the page's own example. [Proof/Lcm.lean](Proof/Lcm.lean) is reused from our own JSP-000260 submission. The Lean development is written from scratch in this package and its predecessor.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's questions. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000263-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
