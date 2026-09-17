# JSP-000910: a binomial coefficient with no small prime factor (scoped certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000910](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000910): *How large must `n` be for `C(n,k)` to have no prime factor smaller than `k`?*

**The open question — the growth of the least such `n` as a function of `k` — is not claimed here.** This package formalizes a fully verified **certificate** at `(n,k) = (23,5)`:

```
C(23,5) = 33649 = 7 · 11 · 19 · 23,
```

which has no prime factor below `5`.

## Statement and proof

```lean
theorem choose_23_5_eq : Nat.choose 23 5 = 33649
theorem choose_23_5_no_small_prime :
    ∀ p : ℕ, p.Prime → p < 5 → ¬ p ∣ Nat.choose 23 5
theorem choose_23_5_coprime_six : Nat.Coprime (Nat.choose 23 5) 6
```

The statement quantifies over all primes below `5` (namely `2` and `3`); `interval_cases` reduces to those and `decide` refutes divisibility of `33649`. Proved without `native_decide`.

`Challenge.lean` is a comparator-style module (the same Mathlib-only statements with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000910.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: a subset of `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (a finite divisibility check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000910-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
