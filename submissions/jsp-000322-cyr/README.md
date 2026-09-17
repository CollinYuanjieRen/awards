# JSP-000322: Erdős #389, the examples n = 2 (k = 5) and n = 3 (k = 4)

This package submits, for intake and eligibility review, a kernel-checked Lean verification of the two examples on the page of [JSP-000322](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000322) / [Erdős Problem #389](https://www.erdosproblems.com/389): is it true that for every `n ≥ 1` there is a `k` with `n(n+1)⋯(n+k−1) ∣ (n+k)⋯(n+2k−1)`?

**Scope statement.** The general question is open and is not addressed; the other computed values (Mehta's table, e.g. `k = 207` for `n = 4`, which formal-conjectures checks with `native_decide`) are not claimed. The problem page records: "For example when `n = 2` we have `k = 5`: `2·3·4·5·6 ∣ 7·8·9·10·11`, and when `n = 3` we have `k = 4`: `3·4·5·6 ∣ 7·8·9·10`." This package verifies these two examples, in the product shape of the formal-conjectures statement of the problem, and additionally that `5` and `4` are the least such `k` (as in the formal-conjectures `IsLeast` statement for `n = 4`, and as recorded in OEIS A375071 cited by the page), by kernel-checked computation without `native_decide`.

## Statements and proof

[Erdos389Examples/Main.lean](Erdos389Examples/Main.lean) proves

```lean
theorem erdos_389_two_five :
    IsLeast {k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (2 + i) ∣ ∏ i ∈ Finset.range k, (2 + k + i)} 5
theorem erdos_389_three_four :
    IsLeast {k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (3 + i) ∣ ∏ i ∈ Finset.range k, (3 + k + i)} 4
```

Proof. `720 ∣ 55440` and `360 ∣ 5040`; minimality by checking `k = 1, …, 4` (resp. `1, …, 3`) with `norm_num` on the explicit products.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound` (no `Lean.ofReduceBool`). [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The examples are the ones recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000322-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
