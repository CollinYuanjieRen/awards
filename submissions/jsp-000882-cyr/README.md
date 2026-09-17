# JSP-000882: a 2n/3 construction lower bound for the "no element divides two others" problem (scoped component)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000882](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000882) (Lebensold, [Le76] *A divisibility problem*): how large can a subset of `{1,…,n}` be if no element divides two other elements?

**The open question — the exact extremal constant `c` (known to lie between `0.6725` and `0.6736`) — is not claimed here.** This package formalizes the clean **construction lower bound** `f(n) ≥ n − ⌊n/3⌋ = ⌈2n/3⌉`: the interval `A = (⌊n/3⌋, n]` has no element dividing two distinct others.

## Statement and proof

```lean
def A (n : ℕ) : Finset ℕ := Finset.Icc (n / 3 + 1) n

theorem A_card (n : ℕ) : (A n).card = n - n / 3
theorem A_no_two_multiples (n : ℕ) :
    ∀ a ∈ A n, ∀ b ∈ A n, ∀ c ∈ A n, b ≠ c → a ∣ b → a ∣ c → a = b ∨ a = c
theorem exists_large_no_div_two (n : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 n ∧ B.card = n - n / 3 ∧
      (∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, b ≠ c → a ∣ b → a ∣ c → a = b ∨ a = c)
```

Every `a ∈ (⌊n/3⌋, n]` satisfies `3a > n`, so any multiple `a·k ≤ n` has `k < 3`; the only multiples of `a` in the interval are `a` itself and `2a`. Hence `a` divides at most one element other than itself, so no element divides two distinct others. The interval has `n − ⌊n/3⌋ = ⌈2n/3⌉` elements.

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and three targets with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000882.md` and the construction note in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the three theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The construction (the top third of the interval) is elementary. No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000882-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
