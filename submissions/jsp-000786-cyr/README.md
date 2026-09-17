# JSP-000786: a run of six consecutive integers with distinct divisor counts (scoped certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000786](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000786): *How long a run of consecutive integers can have pairwise distinct divisor counts?*

**The open question — the growth rate of the longest such run — is not claimed here.** This package formalizes a fully verified **certificate** that a run of length `6` exists: the six consecutive integers `76,77,78,79,80,81` have divisor counts

```
τ(76)=6, τ(77)=4, τ(78)=8, τ(79)=2, τ(80)=10, τ(81)=5,
```

which are pairwise distinct.

## Statement and proof

```lean
def tau (n : ℕ) : ℕ := (Nat.divisors n).card

theorem tau_run_76 : ((List.range 6).map (fun i => tau (76 + i))).Nodup
theorem exists_distinct_tau_run_6 : ∃ m, ((List.range 6).map (fun i => tau (m + i))).Nodup
```

`Nat.divisors n` is Mathlib's finset of divisors of `n`, so `tau` is the divisor-counting function. The `Nodup` of the six-element divisor-count list is decided by `decide` (`native_decide` is not used).

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000786.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (a finite divisor-count check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000786-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
