# JSP-000131: Erdős #124, gcd(d₁, …, d_r) = 1 is necessary in the second question

This package submits, for intake and eligibility review, a Lean proof of the remark on the page of [JSP-000131](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000131) / [Erdős Problem #124](https://www.erdosproblems.com/124): for integers `3 ≤ d₁ < ⋯ < d_r`, can all sufficiently large integers be written as `∑ cᵢaᵢ` with `cᵢ ∈ {0, 1}` and `aᵢ` having only the digits `0, 1` in base `dᵢ` (first question; solved), and, with `aᵢ` divisible by `dᵢ^k` for `k ≠ 0` and `gcd(dᵢ) = 1`, likewise (second question, Burr–Erdős–Graham–Li; open)?

**Scope statement.** Neither question, nor the `∑ 1/(dᵢ − 1) ≥ 1` condition, nor the Burr–Erdős–Graham–Li `(3, 4, 7)` result is addressed. The problem page records: "It is trivial that `gcd(d₁, …, d_r) = 1` is a necessary condition in the second question." This package proves that remark, with the formal-conjectures definition `Erdos124.sumsOfDistinctPowers` copied verbatim from the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/124.lean) and the hypothesis in the shape of its statement `erdos124.ne_zero` (a pointwise sum of sets, `D.gcd id`); the theorem statement is ours.

## Statement and proof

[Erdos124GcdNecessary/Main.lean](Erdos124GcdNecessary/Main.lean) proves

```lean
theorem erdos_124_gcd_eq_one_of_eventually (k : ℕ) (hk : k ≠ 0) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 3 ≤ d) (h : ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k) :
    D.gcd id = 1
```

together with a closed form used by our internal audit tooling.

Proof. For `k ≥ 1` every element of `sumsOfDistinctPowers d k` is divisible by `d`, hence by `g = gcd D`, so every element of the pointwise sum is divisible by `g`. If `g ≠ 1` the integers `≡ 1 (mod g)` are never represented (and if `g = 0`, i.e. `D = ∅`, only `0` is), contradicting the hypothesis that all large integers are.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definition by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The remark is the one recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000131-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
