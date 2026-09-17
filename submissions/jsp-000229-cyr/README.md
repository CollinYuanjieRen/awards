# JSP-000229: Erdős #265, Cantor's sequence a_n = C(n, 2) has both reciprocal sums rational

This package submits, for intake and eligibility review, a Lean proof of the classical example recorded on the page of [JSP-000229](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000229) / [Erdős Problem #265](https://www.erdosproblems.com/265): how fast can an increasing sequence of integers `1 ≤ a₁ < a₂ < ⋯` grow if both `∑ 1/aₙ` and `∑ 1/(aₙ − 1)` are rational?

**Scope statement.** The growth question (Erdős's beliefs; the Kovač–Tao doubly exponential construction; the remaining `limsup` question) is not addressed. The problem page records: "Cantor observed that `aₙ = C(n, 2)` is such a sequence." This package proves that observation. Formal-conjectures has no file for #265, so the theorem statement is ours; it uses Mathlib's `HasSum` so that both series are genuinely convergent (Mathlib's `tsum` of a non-summable family would be `0`, which we deliberately avoid).

## Statement and proof

[Erdos265Cantor/Main.lean](Erdos265Cantor/Main.lean) proves

```lean
theorem erdos_265_cantor :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 2 ≤ a n) ∧
      (∃ q : ℚ, HasSum (fun n ↦ (1 : ℝ) / (a n : ℝ)) (q : ℝ)) ∧
      (∃ q : ℚ, HasSum (fun n ↦ (1 : ℝ) / ((a n : ℝ) - 1)) (q : ℝ))
```

with witness `a n = (n + 3).choose 2 = 3, 6, 10, 15, …`, i.e. Cantor's `C(n, 2)` for `n ≥ 3` (the term `C(2, 2) = 1` would make `aₙ − 1 = 0`, so the sequence starts at `C(3, 2)`; the problem requires `a₁ ≥ 1`, and all terms here are at least `3`). The sums are `1` and `11/9`: `1/C(n+3, 2) = 2/(n+2) − 2/(n+3)` and `1/(C(n+3, 2) − 1) = (2/3)(1/(n+1) − 1/(n+4))` telescope.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The example is Cantor's, as recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000229-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
