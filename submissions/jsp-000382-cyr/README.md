# JSP-000382: 70 is a weird number (scoped certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000382](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000382): *Are there odd weird numbers? Are infinitely many weird numbers primitive?* A **weird** number is abundant (its proper divisors sum to more than itself) yet not semiperfect (no subset of its proper divisors sums to itself).

**The open questions — whether odd weird numbers exist, and whether infinitely many weird numbers are primitive — are not claimed here.** This package formalizes a fully verified **certificate** that a weird number exists: `70` is weird.

Proper divisors of `70` are `{1, 2, 5, 7, 10, 14, 35}`, summing to `74 > 70` (abundant), and no subset of them sums to exactly `70` (all `2^7 = 128` subsets checked), so `70` is not semiperfect.

## Statement and proof

```lean
def IsWeird (n : ℕ) : Prop :=
  n < ∑ d ∈ n.properDivisors, d ∧
  ¬ ∃ S ∈ (n.properDivisors).powerset, ∑ d ∈ S, d = n

theorem seventy_abundant : 70 < ∑ d ∈ (70:ℕ).properDivisors, d
theorem seventy_not_semiperfect :
    ¬ ∃ S ∈ ((70:ℕ).properDivisors).powerset, ∑ d ∈ S, d = 70
theorem seventy_isWeird : IsWeird 70
```

`Nat.properDivisors` is Mathlib's proper-divisor finset. Both facts are decided by `decide` over the seven proper divisors and their `128`-element powerset (`native_decide` is not used; the non-semiperfect check raises `maxRecDepth` only).

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and target with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000382.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the three theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (a finite divisor and subset-sum check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000382-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
