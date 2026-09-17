# JSP-000646: a subset whose pairwise sums avoid the set (scoped construction certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000646](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000646): *How large a subset of an arbitrary finite (real) set can have all pairwise sums outside the set?* (an Erdős–Moser sum-avoiding problem).

**The open question — the guaranteed size / growth rate of such a subset — is not claimed here.** This package formalizes a fully verified **construction certificate**: for every nonempty finite `A ⊆ ℕ`, the top-half subset `{a ∈ A : max A < 2a}` has all pairwise sums outside `A`.

## Statement and proof

```lean
theorem sum_avoiding (A : Finset ℕ) (hA : A.Nonempty) :
    ∀ x ∈ A.filter (fun a => A.max' hA < 2 * a),
    ∀ y ∈ A.filter (fun a => A.max' hA < 2 * a), x + y ∉ A
```

Each element of the filtered subset exceeds `(max A)/2`, so any two (including a repeat) sum to more than `max A`, hence the sum lies outside `A`. Proved from `Finset.le_max'` and `omega`.

`Challenge.lean` is a comparator-style module (the same Mathlib-only statement with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000646.md` and the construction note in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the theorem: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The construction (the top half of the set is sum-avoiding) is elementary. No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000646-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
