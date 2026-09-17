# JSP-000680: the finite lower bound h(18) ≥ 3 (scoped component of Erdős #824)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000680](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000680) (Erdős Problem [#824](https://www.erdosproblems.com/824)): let `h(x)` count the integers `1 ≤ a < b < x` with `(a,b) = 1` and `σ(a) = σ(b)` (`σ` = sum of divisors); is `h(x) > x^{2−o(1)}`?

**The growth question is open** (Pollack–Pomerance proved `h(x)/x → ∞`; the `x^{2−o(1)}` bound is open; these asymptotic results are not claimed). This package formalizes the exact finite fact **`h(18) ≥ 3`**, witnessed by three coprime pairs with equal divisor sum: `(6, 11)` with `σ = 12`, `(14, 15)` with `σ = 24`, and `(10, 17)` with `σ = 18`.

## Statement and proof

With `h x := #{ (a,b) : 1 ≤ a < b < x, (a,b)=1, σ(a)=σ(b) }` (Mathlib's `σ = ArithmeticFunction.sigma 1`), the package proves

```lean
theorem three_le_h_eighteen : 3 ≤ h 18
```

by exhibiting the three pairs `(6,11), (14,15), (10,17)` as distinct members of the counted set (each with `1 ≤ a < b < 18`, coprime, and equal `σ` — all verified by evaluation), so the cardinality is at least `3`.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definition and target with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/824, retrieved 2026-09-17) is recorded verbatim in `sources/erdos824-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of `three_le_h_eighteen`: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution and submission status

The pairs are an elementary finite check. The formalization was authored independently (no known prior Lean formalization of #824), with Claude (Anthropic) assistance and locally checked. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000680-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
