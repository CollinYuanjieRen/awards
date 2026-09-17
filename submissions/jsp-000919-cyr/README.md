# JSP-000919: a sum of distinct factorials that is a perfect power (scoped certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000919](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000919): *Are only finitely many sums of distinct factorials perfect powers (or powerful numbers)?*

**The open finiteness question is not claimed here.** This package formalizes a fully verified **certificate** that a sum of distinct factorials is a perfect power:

```
1! + 2! + 3! = 1 + 2 + 6 = 9 = 3².
```

## Statement and proof

```lean
theorem factorial_sum_eq : Nat.factorial 1 + Nat.factorial 2 + Nat.factorial 3 = 9
theorem factorial_sum_perfect_square :
    Nat.factorial 1 + Nat.factorial 2 + Nat.factorial 3 = 3 ^ 2
theorem exists_factorial_sum_perfect_power :
    ∃ (a b c m k : ℕ), a < b ∧ b < c ∧ 2 ≤ k ∧
      Nat.factorial a + Nat.factorial b + Nat.factorial c = m ^ k
```

The `a < b < c` enforces three distinct factorials and `2 ≤ k` a genuine perfect power (excluding the trivial `k = 1`). Proved by `decide` (`native_decide` not used).

`Challenge.lean` is a comparator-style module (the same Mathlib-only statements with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000919.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: a subset of `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (a finite arithmetic check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000919-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
