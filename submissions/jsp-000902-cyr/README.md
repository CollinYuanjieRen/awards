# JSP-000902: Erdős #1085, Lenz's construction f_d(n) ≥ ((p−1)/(2p)) n² − O(1) for d ≥ 4

This package submits, for intake and eligibility review, a Lean proof of the known lower bound in [JSP-000902](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000902) / [Erdős Problem #1085](https://www.erdosproblems.com/1085): let `f_d(n)` be the maximal number of pairs at distance exactly `1` among `n` points of `ℝ^d`.

**Scope statement.** The planar and three-dimensional questions are open. The problem page records that a construction of Lenz (points on orthogonal circles) shows, for `d ≥ 4`, `f_d(n) ≥ ((p−1)/(2p)) n² − O(1)` with `p = ⌊d/2⌋`. This package proves exactly that bound (with the explicit constant `p/8`); Erdős's matching upper bound and the questions for `d ≤ 3` are not claimed.

## Statement and proof

[Erdos1085Lenz/Main.lean](Erdos1085Lenz/Main.lean) copies the definitions `unitDistNum` (from the formal-conjectures helper library) and `f` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1085.lean) verbatim and proves

```lean
theorem erdos_1085_lower_d4_lenz {d : ℕ} (hd : 4 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 - C ≤ f d n
```

which is exactly the formal-conjectures statement `Erdos1085.erdos_1085.variants.lower_d4_lenz` (tagged "research solved" with `sorry`), via the data-binder form `lenz_lower_bound`.

Proof. Distribute the `n` points as evenly as possible over `p = ⌊d/2⌋` circles of radius `1/√2` lying in the orthogonal coordinate planes `(2j, 2j+1)` (distinct points on a circle via the rational parametrisation `((1−t²)/(1+t²), 2t/(1+t²))/√2`). Two points on different circles are at distance exactly `1`, so the number of unit pairs is at least `∑_{j<k} n_j n_k = (n² − ∑ n_j²)/2 ≥ ((p−1)/(2p)) n² − p/8`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definition by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The construction is Lenz's, as recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000902-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
