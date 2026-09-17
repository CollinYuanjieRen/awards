# JSP-000557: the trivial bound ω(C(n,k)) ≥ log C(n,k) / log n (Erdős #685, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000557](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000557) / [Erdős Problem #685](https://www.erdosproblems.com/685): for `n^ε < k ≤ n^{1−ε}`, is the number of distinct prime divisors of `C(n,k)` equal to `(1+o(1)) k Σ_{k<p<n} 1/p`? The component formalized here is the bound recorded on the problem page as trivial, **"the number of prime factors is > log C(n,k) / log n"**, in its correct non-strict form: every prime power `p^{v_p(C(n,k))}` dividing `C(n,k)` is at most `n` (Kummer/Legendre, Mathlib's `Nat.pow_factorization_choose_le`), so `C(n,k) ≤ n^{ω(C(n,k))}` and `ω(C(n,k)) ≥ log C(n,k) / log n` for `n ≥ 2`. The page's strict inequality fails in degenerate cases (`n = 2`, `k = 1`), which the package records. The asymptotic question and the asymptotic-equality remark are **not** claimed.

## Statements

Every object is Mathlib's: `Nat.choose`, `Nat.primeFactors` (so `(m).primeFactors.card` is `ω(m)`), `Nat.factorization` (the `p`-adic valuation) and `Real.log`; there are no definitions of our own (namespace `Erdos685`, [Proof/Main.lean](Proof/Main.lean)):

```lean
theorem choose_le_pow_card_primeFactors (n k : ℕ) :
    n.choose k ≤ n ^ (n.choose k).primeFactors.card

theorem log_choose_le_card_mul_log (n k : ℕ) :
    Real.log (n.choose k) ≤ ((n.choose k).primeFactors.card : ℝ) * Real.log n

theorem log_choose_div_log_le_card (n k : ℕ) (hn : 2 ≤ n) :
    Real.log (n.choose k) / Real.log n ≤ ((n.choose k).primeFactors.card : ℝ)

theorem strict_fails_two_one :
    Real.log (Nat.choose 2 1) / Real.log 2 = ((Nat.choose 2 1).primeFactors.card : ℝ)

theorem pow_factorization_choose_le' (n k p : ℕ) (hn : 0 < n) :
    p ^ (n.choose k).factorization p ≤ n
```

The first theorem (data binders `n`, `k`, no hypotheses) is the multiplicative form `C(n,k) ≤ n^{ω(C(n,k))}`; the second is its logarithmic form for every `n` (with Lean's convention `log 0 = 0`); the third is the page's form `ω ≥ log C / log n` for `n ≥ 2`; the fourth records that equality, hence failure of the page's strict inequality, occurs at `n = 2`, `k = 1`; the fifth restates the prime-power input with explicit binders. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Write `C(n,k) = Π_{p | C(n,k)} p^{v_p(C(n,k))}`. By Kummer's theorem each factor is at most `n`, so the product is at most `n^{ω(C(n,k))}`. Taking logarithms gives `log C(n,k) ≤ ω(C(n,k)) · log n`, and dividing by `log n > 0` for `n ≥ 2` gives the page's bound. For `n = 2`, `k = 1` both sides equal `1`.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the Mathlib definitions used and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's (Er79d). The bound is the folklore observation recorded on the problem page; its prime-power input is Kummer's theorem, taken from Mathlib. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000557-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
