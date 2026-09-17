# JSP-000649: a ⌈N/2⌉ construction with no element a sum of distinct others (scoped component)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000649](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000649): *How large a subset of a finite integer set can have no element equal to a sum of distinct other elements?*

**The open question — the extremal size and its asymptotics — is not claimed here.** This package formalizes the clean **construction lower bound** `⌈N/2⌉`: the interval `A = (⌊N/2⌋, N]` has no element equal to the sum of a nonempty set of distinct other elements.

## Statement and proof

```lean
def A (N : ℕ) : Finset ℕ := Finset.Icc (N / 2 + 1) N

theorem A_card (N : ℕ) : (A N).card = N - N / 2
theorem A_no_subset_sum (N : ℕ) :
    ∀ a ∈ A N, ∀ T ⊆ (A N).erase a, T.Nonempty → a ≠ T.sum id
theorem exists_large_subset_sum_free (N : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 N ∧ B.card = N - N / 2 ∧
      (∀ a ∈ B, ∀ T ⊆ B.erase a, T.Nonempty → a ≠ T.sum id)
```

Every element exceeds `N/2`, so a single other element is distinct from `a`, while any two or more of them sum to more than `N ≥ a`; hence no element is the sum of a nonempty set of distinct others. The interval has `N − ⌊N/2⌋ = ⌈N/2⌉` elements.

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and three targets with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000649.md` and the construction note in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the three theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The construction (the top half of the interval) is elementary. No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000649-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
