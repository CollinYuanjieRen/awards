# JSP-000634: a Sidon set of six squares (scoped construction certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000634](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000634): *How large a Sidon set can be chosen among the squares in a prescribed range?*

**The open question — the maximum size or density of a Sidon subset of the squares in `[1,N]` — is not claimed here.** This package formalizes a fully verified **construction certificate**: the six perfect squares `{1, 4, 9, 16, 25, 36} = {1², …, 6²}` form a Sidon set (all pairwise sums are distinct).

## Statement and proof

```lean
def S : Finset ℕ := {1, 4, 9, 16, 25, 36}

theorem S_sidon :
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + b = c + d → ({a, b} : Finset ℕ) = {c, d}
theorem S_all_squares : ∀ x ∈ S, ∃ k, x = k ^ 2
```

`S_sidon` is the genuine Sidon (B₂) property, decided over the explicit finset by `decide`; `S_all_squares` exhibits each element as a square. (The full set of squares is not Sidon, e.g. `1² + 8² = 4² + 7² = 65`; this certificate exhibits only a Sidon subset.)

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000634.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The construction is elementary (a finite Sidon check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000634-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
