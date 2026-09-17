# JSP-000213: Erdős #242 (Erdős–Straus), 4/n is a sum of at most four distinct unit fractions

This package submits, for intake and eligibility review, a Lean proof of the elementary remark on the page of [JSP-000213](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000213) / [Erdős Problem #242](https://www.erdosproblems.com/242), the Erdős–Straus conjecture: for every `n > 2`, are there distinct `x < y < z` with `4/n = 1/x + 1/y + 1/z`?

**Scope statement.** The three-term conjecture and all partial results on it are not addressed. The problem page records: "The existence of a representation of `4/n` as the sum of at most four distinct unit fractions follows trivially from a greedy algorithm." This package proves exactly that remark for the problem's range `n > 2`. The formal-conjectures file for #242 states only the three-term conjecture, so the theorem statement is ours.

## Statement and proof

[Erdos242FourFractions/Main.lean](Erdos242FourFractions/Main.lean) proves

```lean
theorem erdos_242_four_unit_fractions (n : ℕ) (hn : 2 < n) :
    ∃ S : Finset ℕ, (∀ s ∈ S, 0 < s) ∧ S.card ≤ 4 ∧ (4 / n : ℚ) = ∑ s ∈ S, (1 : ℚ) / s
```

(a finset of at most four positive integers, hence distinct denominators, whose reciprocals sum to `4/n`), together with the hypothesis-free form for `n + 3` used by our internal audit tooling.

Proof (greedy). For `0 < a/b ≤ 1`, the greedy step subtracts `1/q` with `q = ⌈b/a⌉`; the remainder `(aq − b)/(bq)` has a smaller numerator, and the next greedy denominator exceeds `q`, so the denominators stay distinct. Starting from `4/n` with `n ≥ 4`, at most four steps reach `0`; the case `n = 3` is `4/3 = 1 + 1/3`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The remark is the elementary observation recorded on the problem page (the greedy, or Fibonacci–Sylvester, algorithm). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000213-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
