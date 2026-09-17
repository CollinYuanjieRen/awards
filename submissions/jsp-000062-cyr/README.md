# JSP-000062: the elementary Erdős–Turán upper bound for Sidon sets (scoped component of Erdős #30)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000062](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000062) (Erdős Problem [#30](https://www.erdosproblems.com/30), the **$1000** Sidon-set problem): if `A ⊆ {1,…,N}` is a Sidon set (a B₂ set: all pairwise sums are distinct), how large can `|A|` be?

**The full open $1000 question — whether the maximum size is `N^{1/2} + O_ε(N^ε)` — and the sharp Erdős–Turán error term `N^{1/2} + N^{1/4} + 1` are not claimed here.** This package formalizes the clean elementary **Erdős–Turán upper bound**: a Sidon set in `{1,…,N}` has at most `N − 1` unordered pairs, hence `|A| ≤ sqrt(2N) + O(1)`.

## Statement and proof

With `IsSidon A := ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → a = c ∨ a = d`, the package proves

```lean
theorem choose_two_le {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon A) : A.card.choose 2 ≤ N - 1
theorem card_mul_pred_le {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon A) : A.card * (A.card - 1) ≤ 2 * (N - 1)
```

The `C(|A|, 2)` positive differences `b − a` (over the two-element subsets of `A`) are **distinct**: if `b − a = d − c` with `a < b`, `c < d`, then `a + d = b + c`, so the Sidon property forces `a = c` and `b = d`. These distinct differences all lie in `{1,…,N−1}`, a set of `N − 1` elements. Formally, each two-element subset (an element of `A.powersetCard 2`, whose cardinality is `A.card.choose 2` by `Finset.card_powersetCard`) is mapped injectively to `max' − min' ∈ Finset.Icc 1 (N−1)` via `Finset.card_le_card_of_injOn`, giving `A.card.choose 2 ≤ N − 1`. The doubled form follows from `Nat.choose_two_right` and the parity of `n·(n−1)`.

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/30, retrieved 2026-09-17) is recorded verbatim in `sources/erdos30-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The upper bound (distinct differences) is the classical elementary Erdős–Turán argument. No third-party Lean formalization of this specific scoped bound for the record is known to the author; this package was authored independently. (An external arXiv development formalizes Sidon-set infrastructure and Singer's *lower* bound, a different result and not a submission here.) Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000062-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
