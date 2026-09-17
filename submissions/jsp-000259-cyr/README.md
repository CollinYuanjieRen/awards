# JSP-000259: the N = 6 representable-integer instance (scoped component of Erdős #308)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000259](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000259) (Erdős Problem [#308](https://www.erdosproblems.com/308), Erdős–Graham): for `N ≥ 1`, what is the smallest integer not representable as a sum of distinct unit fractions with denominators from `{1,…,N}`, and does the set of representable integers have the shape `{1,…,m}`?

The general problem was solved asymptotically by Croot (1999); **those asymptotic bounds are not claimed here.** This package formalizes the exact **`N = 6` instance**: the representable positive integers are exactly `{1, 2}`, so the smallest non-representable positive integer is `3`, and the representable set has the shape `{1,…,2}` — a concrete verified instance of both questions on the page.

## Statement and proof

With `Representable N k := ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ ∑ n ∈ S, (1 : ℚ)/n = k` (a set `S` of distinct denominators from `{1,…,N}` whose unit fractions sum to the integer `k`), the package proves

```lean
theorem representable_one {N : ℕ} (hN : 1 ≤ N) : Representable N 1
theorem representable_two_six : Representable 6 2
theorem not_representable_ge_three_six {k : ℕ} (hk : 3 ≤ k) : ¬ Representable 6 k
theorem representable_six_iff {k : ℕ} (hk : 1 ≤ k) : Representable 6 k ↔ k = 1 ∨ k = 2
```

`1` is `∑_{n∈{1}} 1/n`; `2` is `1 + 1/2 + 1/3 + 1/6` (denominators `{1,2,3,6}`). No sum can reach `3` because every subset sum is bounded by `∑_{n=1}^{6} 1/n = 49/20 = 2.45 < 3` (monotonicity of the sum over subsets, terms nonnegative). Hence the representable positive integers are exactly `{1, 2}`.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definition and `representable_six_iff` with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/308, retrieved 2026-09-17) is recorded verbatim in `sources/erdos308-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the four theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The general problem is Erdős–Graham's (solved by Croot); the `N = 6` instance is an elementary finite check. **Prior art:** an independent Lean formalization of Erdős #308 exists in the public third-party repository plby/lean-proofs; this package was authored independently, without reading or copying that source. Prepared with Claude (Anthropic) assistance and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000259-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
