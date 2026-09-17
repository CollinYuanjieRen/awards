# JSP-000303: Erdős #367, the trivial bound ∏_{n ≤ m < n+k} B₂(m) ≪ n² for k ≤ 2

This package submits, for intake and eligibility review, a Lean proof of a small settled component of [JSP-000303](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000303) / [Erdős Problem #367](https://www.erdosproblems.com/367): with `B₂(n)` the powerful (2-full) part of `n`, is it true that for every fixed `k ≥ 1`, `∏_{n ≤ m < n+k} B₂(m) ≪ n^{2+o(1)}`?

**Scope statement.** The question is open. The problem page records van Doorn's remark that for `k ≤ 2` one trivially has `∏_{n ≤ m < n+k} B₂(m) ≪ n²`, while this fails for every `k ≥ 3`. This package proves exactly the `k ≤ 2` bound; the open question and the `k ≥ 3` behaviour are not claimed. The separate submission PR #374 on this record formalizes a different component (a logarithmic lower bound for `k ≥ 3`); the two do not overlap.

## Statement and proof

[Erdos367PowerfulParts/Main.lean](Erdos367PowerfulParts/Main.lean) copies the definition `B` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/367.lean) verbatim and proves

```lean
theorem erdos_367_k_le_two : ∀ k : ℕ, k ≤ 2 →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ)
```

which is exactly the formal-conjectures statement `Erdos367.erdos_367.variants.k_le_two` (tagged "research solved" with `sorry`), via the `k = 2` instance `erdos_367_two` and the lemma `B_dvd : B r n ∣ n`.

Proof. The `r`-full part is a sub-product of the prime factorization, so `B₂(m) ∣ m` and `B₂(m) ≤ m` for `m ≥ 1`; a product over at most two consecutive integers is therefore at most `n(n+1) ≤ 2n²`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definition by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The remark is van Doorn's (problem page comments). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000303-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
