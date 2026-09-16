# JSP-000257: Erdős #306, the instance a/b = 1 — Watanabe's 47-term semiprime certificate

This package submits, for intake and eligibility review, a Lean certificate of the known instance `a/b = 1` of [JSP-000257](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000257) / [Erdős Problem #306](https://www.erdosproblems.com/306): is every positive rational `a/b` with `b` squarefree a sum of distinct unit fractions whose denominators are products of two distinct primes?

**Scope statement.** The general question is open. What is known for `a/b = 1` is a family of explicit decompositions (Barbeau 1977, Johnson 1978, and the shortest known, with 47 terms, by Watanabe 2020). This package certifies Watanabe's first 47-term decomposition and nothing more. It is a component contribution to the record; no closure of the general question is claimed.

## Statement and proof

[Erdos306One/Main.lean](Erdos306One/Main.lean) proves `erdos_306_one`:

```lean
theorem erdos_306_one :
    ∃ k : ℕ, ∃ n : Fin (k + 1) → ℕ, n 0 = 1 ∧ StrictMono n ∧
      (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
      (1 : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i)
```

This is exactly the instance `q = 1` of the [formal-conjectures statement of Erdős #306](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/306.lean): a strictly increasing sequence `1 = n 0 < n 1 < ⋯ < n k` in which every `n i` with `i ≥ 1` has exactly two distinct prime factors, each to the first power (`ω (n i) = 2 ∧ Ω (n i) = 2`, Mathlib's `ArithmeticFunction.cardDistinctFactors` and `cardFactors`), and whose reciprocals sum to `1` in `ℚ`. The witness is `k = 47` with Watanabe's denominators

```
6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 82, 85, 86, 87, 91,
93, 95, 106, 111, 123, 133, 145, 155, 159, 185, 203, 215, 253, 265, 287, 319, 493, 583, 731, 851, 1073
```

(arXiv:2009.03275, §3.3, first example). Every fact (primality of the 16 primes up to 53, the 47 factorizations, monotonicity, and the exact rational sum) is proved in Lean by kernel-checked arithmetic; no `native_decide` or external computation is trusted.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints its axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The decomposition is Watanabe's (arXiv:2009.03275); earlier examples are due to Barbeau (1977) and Johnson (1978). The Lean certificate was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000257-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
