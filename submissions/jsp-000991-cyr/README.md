# JSP-000991: a 2-colouring of {1,…,8} with no monochromatic 3-term progression (scoped exact-value certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000991](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000991): the minimum number `V(n)` of monochromatic arithmetic progressions in a 2-colouring of `{1,…,n}` (Graham's problem).

**The open question — the asymptotic constant `β` in `V(n) = β n²(1+o(1))` — is not claimed here.** This package formalizes the exact boundary value for 3-term progressions at `n = 8`: `V₃(8) = 0`, i.e. there is a 2-colouring of `{1,…,8}` with **no** monochromatic 3-term arithmetic progression (equivalently the van der Waerden fact `W(2;3) > 8`; at `n = 9` every 2-colouring has one). The witness colours `{2,4,5,7}` with one colour and `{1,3,6,8}` with the other.

## Statement and proof

```lean
def col (n : ℕ) : Bool := n == 2 || n == 4 || n == 5 || n == 7

theorem no_mono_3ap :
    ∀ a ∈ Finset.Icc 1 8, ∀ d ∈ Finset.Icc 1 8, a + 2 * d ≤ 8 →
      ¬ (col a = col (a + d) ∧ col (a + d) = col (a + 2 * d))

theorem exists_2col_no_mono_3ap :
    ∃ c : ℕ → Bool, ∀ a ∈ Finset.Icc 1 8, ∀ d ∈ Finset.Icc 1 8, a + 2 * d ≤ 8 →
      ¬ (c a = c (a + d) ∧ c (a + d) = c (a + 2 * d))
```

The quantification `a ≥ 1, d ≥ 1, a + 2d ≤ 8` ranges over every 3-term progression with positive common difference inside `{1,…,8}` (twelve of them). Both theorems are closed by kernel `decide` (standard `Finset` decidability instances; no `native_decide`).

`Challenge.lean` is a comparator-style module (the same Mathlib-only statements with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000991.md` and the witness note in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of both theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The fact `W(2;3) = 9` is classical; the colouring is the standard witness. No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000991-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
