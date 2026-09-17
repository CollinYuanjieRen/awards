# JSP-000255: a rational as a sum of three distinct unit fractions (scoped certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000255](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000255): *What is the minimum number of distinct positive unit fractions needed to represent a given positive rational?*

**The open question — the exact minimum over all rationals (an Erdős–Straus-flavored problem) — is not claimed here, and minimality for this instance is not asserted.** This package formalizes a fully verified **upper-bound certificate**: the rational `4/5` is a sum of three distinct unit fractions,

```
4/5 = 1/2 + 1/4 + 1/20.
```

## Statement and proof

```lean
theorem four_fifths_eq : (1:ℚ)/2 + 1/4 + 1/20 = 4/5
theorem exists_three_distinct_unit_fractions :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ (1:ℚ)/a + 1/b + 1/c = 4/5
```

The summands are genuine unit fractions `1/a` with positive natural denominators, and `0 < a < b < c` enforces three distinct denominators. Proved by `norm_num` (`native_decide` not used).

`Challenge.lean` is a comparator-style module (the same Mathlib-only statements with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000255.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (an exact rational identity). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000255-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
