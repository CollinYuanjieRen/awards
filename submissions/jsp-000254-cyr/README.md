# JSP-000254: Erdős #302, the lower bounds f(N) ≥ (1/2 − o(1))N and Cambie's f(N) ≥ (5/8 − o(1))N

This package submits, for intake and eligibility review, Lean proofs of the known lower bounds in [JSP-000254](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000254) / [Erdős Problem #302](https://www.erdosproblems.com/302): let `f(N)` be the size of the largest `A ⊆ {1, …, N}` with no solution to `1/a = 1/b + 1/c` in distinct `a, b, c ∈ A`; estimate `f(N)`.

**Scope statement.** The order of `f(N)` is open (van Doorn proved `f(N) ≤ (9/10 + o(1))N`). The problem page records that the odd integers, or the integers in `[N/2, N]`, give `f(N) ≥ (1/2 + o(1))N`, and that Stijn Cambie observed `f(N) ≥ (5/8 + o(1))N` by taking the odd integers `≤ N/4` together with all integers in `[N/2, N]`. This package proves Cambie's construction with an explicit error term and derives both lower-bound statements; the upper bound and the true order of `f(N)` are not claimed.

## Statement and proof

[Erdos302Cambie/Main.lean](Erdos302Cambie/Main.lean) copies the definitions `NoUnitFractionTriple` and `IsMaxNoTripleCard` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/302.lean) verbatim and proves

```lean
theorem erdos_302_five_eighths_explicit (N : ℕ) :
    ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ (5 * N : ℝ) / 8 - 2 ≤ A.card
```

with the witness `cambieSet N` (odd integers `≤ N/4` and all integers `a` with `N/2 < a ≤ N`), and from it `erdos_302_lower_five_eighths` and `erdos_302_lower_half`, which are exactly the formal-conjectures statements `Erdos302.erdos_302.variants.lower_five_eighths` and `lower_half` (tagged "research solved" with `sorry`).

Proof. Suppose `1/a = 1/b + 1/c` with distinct `a, b, c` in the set, so `bc = a(b + c)` and `a < b, c`. If `a > N/2` then `1/a < 2/N ≤ 1/b + 1/c`. If `a` is odd and one of `b, c` is odd, the equation `bc = a(b + c)` is odd on one side and even on the other. Otherwise `b, c` are even, hence `> N/2`, and `1/b + 1/c < 4/N ≤ 1/a`. The set has at least `(N − 3)/8 + N/2 ≥ 5N/8 − 2` elements.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definition by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The 5/8 construction is Stijn Cambie's (recorded on the problem page); the 1/2 bound is folklore. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000254-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
