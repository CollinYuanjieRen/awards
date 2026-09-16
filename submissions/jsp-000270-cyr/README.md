# JSP-000270: Erdős #324, the settled low-degree cases (no polynomial of degree ≤ 2, and not x⁴)

This package submits, for intake and eligibility review, a Lean proof of the settled part of [JSP-000270](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000270) / [Erdős Problem #324](https://www.erdosproblems.com/324): is there a polynomial `f ∈ ℤ[x]` such that all sums `f(a) + f(b)` with `a < b` nonnegative integers are distinct?

**Scope statement.** The question is open (probably `x⁵` works; the cubic case was excluded by Dubickas–Novikas in 2021). The problem page records two settled facts: "it is easy to check that a quadratic `f` cannot have this property" and "it is a classical fact that `x⁴` cannot have this property". This package proves exactly these two facts, strengthened from "quadratic" to "degree at most two" (constant and linear `f` fail trivially). Nothing about cubic or higher-degree polynomials, and nothing about the general question, is claimed.

## Statement and proof

[Erdos324LowDeg/Main.lean](Erdos324LowDeg/Main.lean) proves

```lean
theorem erdos_324_low_degree_and_quartic :
    ¬ ∃ f : ℤ[X], (f.natDegree ≤ 2 ∨ f = X ^ 4) ∧
      {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => f.eval (a : ℤ) + f.eval (b : ℤ)
```

The injectivity clause is token-for-token the one in the [formal-conjectures rendering `Erdos324.erdos_324`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/324.lean) (`∃ f : ℤ[X], {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => f.eval (a : ℤ) + f.eval (b : ℤ)`, open with `sorry`), so the theorem is a direct constraint on any witness of that statement: it must have degree at least three and differ from `X ^ 4`. The two components are the named theorems `not_sidonPoly_of_natDegree_le_two` and `not_sidonPoly_X_pow_four`.

Proof. Write `f = p x² + q x + r`. If `p = q = 0` the pairs `(0, 1)`, `(0, 2)` collide; if `p = 0 ≠ q` the pairs `(0, 3)`, `(1, 2)` collide. If `p ≠ 0`, negate `p, q` if necessary so that `p > 0`, put `y = 2p + 1`, `b = y² + y + q²`, `d = y² + q²`, `a = by − 2p² − 2p − 1 + q`, `c = a + 1`; then `0 ≤ d < b < a < c` and `p(a² + b²) + q(a + b) = p(c² + d²) + q(c + d)` is a polynomial identity, so `f(b) + f(a) = f(d) + f(c)` with `(b, a) ≠ (d, c)`. For `x⁴`, Euler's `59⁴ + 158⁴ = 133⁴ + 134⁴ = 635318657`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints its axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The mathematics is elementary and classical (the quartic collision is Euler's). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000270-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
