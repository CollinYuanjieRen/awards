# JSP-000144: an 8-element 3-AP-free subset of {1,…,14} (scoped lower-bound certificate `r₃(14) ≥ 8`)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000144](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000144): the largest size `r_k(N)` of a subset of `{1,…,N}` with no `k`-term arithmetic progression (the Erdős–Turán / Szemerédi problem).

**The open question — the asymptotic size and growth of `r_k(N)` — is not claimed here.** This package formalizes one explicit finite certificate: the 8-element set `S = {1, 2, 4, 5, 10, 11, 13, 14} ⊆ {1,…,14}` contains no nontrivial 3-term arithmetic progression, so `r₃(14) ≥ 8`. (By exhaustive search `S` is the unique 8-element 3-AP-free subset of `{1,…,14}` and no 9-element one exists, so in fact `r₃(14) = 8`; that exact value is a remark, not part of the formalized statement.)

## Statement and proof

```lean
def S : Finset ℕ := {1, 2, 4, 5, 10, 11, 13, 14}

theorem S_ap_free : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + c = 2 * b → a = c

theorem r3_14_ge_8 :
    ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 14 ∧ T.card = 8 ∧
      (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a + c = 2 * b → a = c)
```

`a + c = 2b` with `a ≠ c` is exactly a 3-term progression with nonzero common difference (in either order), so `S_ap_free` says `S` has no nontrivial 3-term progression. `S.card = 8` counts distinct elements. All facts are closed by kernel `decide` (standard `Finset` decidability instances; no `native_decide`).

`Challenge.lean` is a comparator-style module (the same Mathlib-only statements with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000144.md` and the witness note in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is a finite computation, not the Salem–Spencer/Behrend construction. No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000144-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
