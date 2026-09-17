# JSP-000783: two powerful numbers between consecutive squares (scoped certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000783](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000783): *How many powerful numbers can lie between consecutive squares?* (A **powerful** number has every prime factor to exponent at least 2.)

**The open question — the maximum number of powerful numbers between consecutive squares and its asymptotics — is not claimed here.** This package formalizes a fully verified **certificate** that at least two distinct powerful numbers lie strictly between consecutive squares:

```
25 = 5²  <  27 = 3³  <  32 = 2⁵  <  36 = 6².
```

## Statement and proof

```lean
def Powerful (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p

theorem powerful_27 : Powerful 27
theorem powerful_32 : Powerful 32
theorem powerful_pair_between_squares :
    Powerful 27 ∧ Powerful 32 ∧ 5 ^ 2 < 27 ∧ 27 < 32 ∧ 32 < 6 ^ 2
```

`Nat.primeFactors` and `Nat.factorization` are Mathlib's prime-support and prime-exponent functions. Writing `27 = 3³` and `32 = 2⁵`, the prime support is a singleton (`Nat.primeFactors_prime_pow`) and the exponent is the power (`Nat.Prime.factorization_pow`), both `≥ 2`.

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and target with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000783.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the three theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (a finite factorization check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000783-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
