# JSP-000988: Erdős #1183, the chain lower bound f(n) ≥ (n + 1)/2

This package submits, for intake and eligibility review, a Lean proof of the known lower bound in [JSP-000988](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000988) / [Erdős Problem #1183](https://www.erdosproblems.com/1183) (Erdős–Ulam): let `f(n)` be the largest `f` such that every 2-colouring of the subsets of `{1, …, n}` contains a monochromatic family of at least `f` sets closed under unions and intersections; estimate `f(n)`.

**Scope statement.** The problem is open: the order of magnitude of `f(n)` and the questions about the union-closed variant `F(n)` are not addressed. The problem page records the only known lower bound: "it is trivial that `f(n) ≥ (n+1)/2`, since there is a sequence of `n+1` many nested subsets." This package proves exactly that bound. (The problem's forum thread reports 2026 partial results on upper bounds; they do not affect this component and nothing from them is claimed.) There is no formal-conjectures statement of #1183; the definitions are stated from scratch.

## Statement and proof

[Erdos1183Chain/Main.lean](Erdos1183Chain/Main.lean) defines `IsUnionInterClosed F` (`A ∪ B ∈ F` and `A ∩ B ∈ F` for all `A, B ∈ F`), `IsMonochromatic c F` (the colouring `c : Finset (Fin n) → Fin 2` is constant on `F`), and

```lean
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ c : Finset (Fin n) → Fin 2,
    ∃ F : Finset (Finset (Fin n)), IsMonochromatic c F ∧ IsUnionInterClosed F ∧ k ≤ F.card}

theorem erdos_1183_f_lower_bound (n : ℕ) : n + 1 ≤ 2 * f n
```

The set in the definition of `f` is bounded by `2ⁿ`, so `sSup` is its maximum and `f` is the problem's function; `n + 1 ≤ 2 f(n)` is `f(n) ≥ (n + 1)/2` (equivalently `f(n) ≥ ⌈(n+1)/2⌉`). Proof: the initial segments `∅ ⊂ {0} ⊂ ⋯ ⊂ {0, …, n−1}` form a chain of `n + 1` distinct subsets; by the pigeonhole principle some colour class contains more than `n/2` of them (`exists_monochromatic_closed_family`); a subfamily of a chain is closed under unions and intersections because the union and intersection of two comparable sets are the larger and the smaller one.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definition of `f` by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The bound is the trivial one recorded on the problem page (Erdős, 1978). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000988-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
