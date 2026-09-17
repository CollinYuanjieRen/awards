# JSP-000574: Erdős #704, the trivial cube-tiling colouring χ(G_n) ≤ (2 + √n)^n

This package submits, for intake and eligibility review, a Lean proof of the elementary upper bound recorded on the page of [JSP-000574](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000574) / [Erdős Problem #704](https://www.erdosproblems.com/704): let `G_n` be the unit-distance graph of `ℝ^n`; estimate its chromatic number `χ(G_n)`, does it grow exponentially, and does `lim χ(G_n)^{1/n}` exist?

**Scope statement.** The questions are open and are not addressed; the Frankl–Wilson and Raigorodsky lower bounds and the Larman–Rogers upper bound `(3 + o(1))^n` are not claimed. The problem page records: "The trivial colouring (by tiling with cubes) gives `χ(G_n) ≤ (2 + √n)^n`." This package proves that bound. Formal-conjectures has no file for #704, so the definition of `G_n` is ours (a `SimpleGraph` on `EuclideanSpace ℝ (Fin n)` with adjacency `dist x y = 1`).

## Statements and proof

[Erdos704CubeColouring/Main.lean](Erdos704CubeColouring/Main.lean) proves

```lean
theorem erdos_704_trivial_colouring (n : ℕ) :
    ∃ k : ℕ, (unitDistanceGraph n).Colorable k ∧ (k : ℝ) ≤ (2 + Real.sqrt n) ^ n

theorem erdos_704_chromaticNumber_le (n : ℕ) :
    (unitDistanceGraph n).chromaticNumber ≤ (⌊(2 + Real.sqrt n) ^ n⌋₊ : ℕ∞)
```

Proof. Let `m = ⌈√n⌉₊` and colour `x` by the vector of residues `(⌊x_i √n⌋ mod (m + 1))_{i < n}`, a colouring with `(m + 1)^n` colours. If `x` and `y` receive the same colour then for each coordinate either the floors agree, so `|x_i − y_i| < 1/√n`, or they differ by at least `m + 1`, so `|x_i − y_i| > m/√n ≥ 1`. In the first case for all `i`, `dist x y < 1`; otherwise `dist x y > 1`; either way `x` and `y` are not adjacent. Finally `(m + 1)^n ≤ (2 + √n)^n` since `⌈√n⌉₊ < √n + 1`. (For `n = 0` the graph has a single vertex.)

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates both theorems as typed `example`s, unfolds the adjacency relation by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The bound is the trivial colouring recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000574-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
