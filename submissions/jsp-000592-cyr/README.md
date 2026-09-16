# JSP-000592: Erdős #724, two orthogonal Latin squares of order 10 (Euler's conjecture fails at 10)

This package submits, for intake and eligibility review, a Lean certificate for the settled part of [JSP-000592](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000592) / [Erdős Problem #724](https://www.erdosproblems.com/724): with `f(n)` the maximum number of mutually orthogonal Latin squares of order `n`, is `f(n) ≫ n^{1/2}`?

**Scope statement.** The asymptotic question is open and is not addressed. The problem page records that Euler's conjecture `f(n) = 1` for `n ≡ 2 (mod 4)` was disproved by Bose, Parker and Shrikhande (`f(n) ≥ 2` for `n ≥ 7`). This package certifies the smallest disputed order: an explicit pair of orthogonal Latin squares of order 10, hence `f(10) ≥ 2`. The general `n ≥ 7` theorem, and any statement about `f(10) ≥ 3`, are not claimed. There is no formal-conjectures statement of #724; the definitions are stated from scratch.

## Statement and proof

[Erdos724Ten/Main.lean](Erdos724Ten/Main.lean) defines `IsLatinSquare` (every row and every column of `L : Fin n → Fin n → Fin n` is injective, hence a permutation), `IsOrthogonal` (the map `(i, j) ↦ (L i j, M i j)` is injective, i.e. every ordered pair of symbols occurs exactly once), `IsMOLS k S` (`k` Latin squares, pairwise orthogonal), and proves

```lean
theorem erdos_724_two_mols_ten : ∃ S : Fin 2 → Fin 10 → Fin 10 → Fin 10, IsMOLS 2 S
```

The witness is the pair `squareA`, `squareB` of explicit `10 × 10` tables; the Latin property of each and their orthogonality are checked by the kernel with `decide` (no `native_decide`). The pair was found by a short search (a random Latin square and ten disjoint transversals); it is not Parker's historical 1959 pair, and no such claim is made.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints its axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The mathematics (existence of orthogonal Latin squares of order 10) is Parker's (1959) and Bose–Shrikhande–Parker's (1960). The Lean certificate was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000592-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
