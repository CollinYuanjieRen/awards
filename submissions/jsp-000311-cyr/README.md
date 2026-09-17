# JSP-000311: a central binomial coefficient coprime to 105 (scoped certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000311](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000311): *Are infinitely many central binomial coefficients coprime to 105 (equivalently, divisible by none of 3, 5, 7)?*

**The open question — whether infinitely many such coefficients exist — is not claimed here.** This package formalizes a fully verified **certificate** that at least one central binomial coefficient is coprime to `105`: for `n = 10`,

```
C(20,10) = 184756,   gcd(184756, 105) = 1.
```

## Statement and proof

```lean
theorem centralBinom_ten_eq : Nat.centralBinom 10 = 184756
theorem centralBinom_ten_coprime_105 : Nat.Coprime (Nat.centralBinom 10) 105
theorem exists_centralBinom_coprime_105 : ∃ n, 0 < n ∧ Nat.Coprime (Nat.centralBinom n) 105
```

`Nat.centralBinom n = Nat.choose (2n) n`. The value is computed by `rfl`, and `Nat.Coprime (= gcd = 1)` by `decide`; `native_decide` is not used. The existence statement carries `0 < n` so the witness is the genuine `n = 10`, not the trivial `n = 0`.

`Challenge.lean` is a comparator-style module (the same Mathlib-only statements with `sorry`, not imported by the build) for mechanical statement comparison. The catalog record is in `sources/jsp-000311.md` and the numeric witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: a subset of `[propext, Classical.choice, Quot.sound]` (here, no axiom dependence at all). No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (a finite gcd computation). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000311-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
