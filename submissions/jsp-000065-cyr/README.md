# JSP-000065: Erdős #36 (minimum overlap), Erdős's 1955 example limsup M(N)/N ≤ 1/2

This package submits, for intake and eligibility review, a Lean proof of the classical upper example in [JSP-000065](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000065) / [Erdős Problem #36](https://www.erdosproblems.com/36), the minimum overlap problem: split `{1, …, 2N}` into two sets `A, B` of size `N`, let `M(N)` be the least possible value of `max_k #{(a, b) ∈ A × B : a − b = k}`, and let `c = lim M(N)/N`.

**Scope statement.** The value of `c` is open (`0.379005 ≤ c ≤ 0.380926…`). The problem page records that the example (with `N` even) `A = {N/2 + 1, …, 3N/2}` shows `c ≤ 1/2`. This package proves exactly that bound; the sharper upper bounds (Motzkin–Ralston–Selfridge, Haugland), the lower bounds, and the value of `c` are not claimed.

## Statement and proof

[Erdos36MinimumOverlap/Main.lean](Erdos36MinimumOverlap/Main.lean) copies the definitions `Overlap`, `MaxOverlap`, `M` and `MinOverlapQuotient` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/36.lean) verbatim and proves

```lean
theorem two_mul_M_le (N : ℕ) : 2 * M N ≤ N + 1
theorem minimum_overlap_upper_erdos_1955 : atTop.limsup MinOverlapQuotient ≤ (1 : ℝ) / 2
```

the second being exactly the formal-conjectures statement `Erdos36.minimum_overlap.variants.upper.erdos_1955` (tagged "research solved" with `sorry`).

Proof. For every `N` take `A = [⌈N/2⌉ + 1, ⌈N/2⌉ + N]` and `B` its complement in `[1, 2N]`, two intervals of lengths `⌈N/2⌉` and `⌊N/2⌋` separated by a gap of length `N`. For a fixed difference `k`, the pairs `(a, b)` with `a − b = k` inject into `B ∩ (A − k)`, and the interval `A − k` of length `N` meets at most one of the two parts of `B`; hence every overlap is at most `⌈N/2⌉`, so `M(N) ≤ ⌈N/2⌉`, `M(N)/N ≤ 1/2 + 1/(2N)`, and the limsup is at most `1/2`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definitions by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The example is Erdős's (1955). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000065-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
