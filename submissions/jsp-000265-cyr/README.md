# JSP-000265: a minimal zero-sum collection of signed reciprocals (scoped certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000265](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000265): *How large can a minimal nonempty zero-sum collection of signed integer reciprocals be?*

**The open question — the maximum length of such a minimal (irreducible) vanishing collection — is not claimed here.** This package formalizes a fully verified **certificate** that a minimal collection of size 3 exists: the signed reciprocals `{1/2, -1/3, -1/6}` sum to `0`, and no nonempty proper subcollection sums to `0`.

## Statement and proof

```lean
def V : Finset ℚ := {1/2, -1/3, -1/6}

theorem V_sum : ∑ x ∈ V, x = 0
theorem V_minimal : ∀ T ∈ V.powerset, T.Nonempty → T ≠ V → ∑ x ∈ T, x ≠ 0
```

`V_sum` is `1/2 - 1/3 - 1/6 = 0`. For `V_minimal`, `T ∈ V.powerset` ranges over all subcollections, `T.Nonempty` excludes the empty one, and `T ≠ V` makes it proper; the six proper nonempty subsums (`1/2, -1/3, -1/6, 1/6, 1/3, -1/2`) are all nonzero. Proved by rewriting `∑ x ∈ T, x` as `∑ x ∈ V, if x ∈ T then x else 0` and case-splitting on the three memberships (the ℚ `decide`/`powerset` path is not kernel-reducible, so this is done by hand).

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000265.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (exact rational arithmetic over a 3-element collection). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000265-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
