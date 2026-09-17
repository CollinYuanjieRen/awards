# JSP-000069: the elementary N^(1/3) counting bound for distinct-triple-sum sets (scoped component of Erdős #41)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000069](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000069) (Erdős Problem [#41](https://www.erdosproblems.com/41), **$500**, OPEN): if `A ⊆ ℕ` has all triple sums `a+b+c` distinct (aside from trivial coincidences), is `liminf_{N→∞} |A ∩ {1,…,N}| / N^{1/3} = 0`?

**The open $500 question — whether that liminf is zero — is not claimed here.** This package formalizes the underlying elementary **counting upper bound** (the `N^{1/3}` analog of the Sidon `N^{1/2}` bound): a set in `{1,…,N}` whose three-element subsets all have distinct sums has at most `3N` such subsets, hence `|A| = O(N^{1/3})`.

## Statement and proof

With `DistinctTripleSums A := ∀ s ∈ A.powersetCard 3, ∀ t ∈ A.powersetCard 3, s.sum id = t.sum id → s = t` (distinct 3-element subsets have distinct sums), the package proves

```lean
theorem choose_three_le {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hD : DistinctTripleSums A) : A.card.choose 3 ≤ 3 * N
```

The `C(|A|,3)` three-element subset sums are distinct (by hypothesis) and each lies in `{1,…,3N}` (three summands, each in `{1,…,N}`), a set of `3N` integers. So the sum map is an injection of `A.powersetCard 3` (cardinality `A.card.choose 3` by `Finset.card_powersetCard`) into `Finset.Icc 1 (3N)`, giving `A.card.choose 3 ≤ 3N` via `Finset.card_le_card_of_injOn`. This is the elementary counting argument that forces the `N^{1/3}` density scale.

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and target with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/41, retrieved 2026-09-17) is recorded in `sources/erdos41-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the theorem: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The counting bound is the classical elementary argument (the `B_h`-set density bound, here `h = 3`). No third-party Lean formalization of this scoped bound for the record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000069-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
