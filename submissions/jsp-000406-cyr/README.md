# JSP-000406: Erdős #507 (Heilbronn's triangle problem), the elementary bounds 1/n² ≪ α(n) ≪ 1/n

This package submits, for intake and eligibility review, Lean proofs of the two elementary bounds in [JSP-000406](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000406) / [Erdős Problem #507](https://www.erdosproblems.com/507): let `α(n)` be such that every set of `n` points in the unit disk contains three points determining a triangle of area at most `α(n)`; estimate `α(n)`.

**Scope statement.** The order of `α(n)` is open (`log n / n² ≪ α(n) ≪ n^{−8/7−1/2000}` by Komlós–Pintz–Szemerédi and Cohen–Pohoata–Zakharov). The problem page records that "it is trivial that `α(n) ≪ 1/n`" and that "Erdős observed that `α(n) ≫ 1/n²`". This package proves exactly these two bounds; nothing about the true order of `α(n)` is claimed.

## Statement and proof

[Erdos507Heilbronn/Main.lean](Erdos507Heilbronn/Main.lean) copies the definitions `minTriangleArea` and `α` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/507.lean) verbatim, together with the oriented-plane instances and the signed area `EuclideanGeometry.triangle_area` from the formal-conjectures helper library (specialised to `ℝ²`), and proves

```lean
theorem erdos_507_upper_trivial : α =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ))
theorem erdos_507_lower_erdos : (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) =O[atTop] α
```

which are exactly the formal-conjectures statements `Erdos507.erdos_507.variants.upper_trivial` and `lower_erdos` (their notations `≪`, `≫` mean `IsBigO atTop` on functions `ℕ → ℝ`; both tagged "research solved" with `sorry`), plus their conjunction `erdos_507_trivial_bounds`.

Proof. Upper bound: cut the disk into `⌊n/4⌋ + 1` horizontal strips; some strip contains three points, and a triangle inside a strip of height `h` and width `2` has area at most `h`, giving `α(n) ≤ 32/n` for `n ≥ 6`. Lower bound: for a prime `p ∈ (n, 2n]` (Bertrand) the points `(i/(2p), (i² mod p)/(2p))`, `i < n`, lie in the disk and any three of them span a triangle of area at least `1/(8p²) ≥ 1/(32n²)`, because the integer determinant is congruent to `(i−k)(j−k)(j−i) ≢ 0 (mod p)`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definition of `α` by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The upper bound is folklore and the lower-bound construction is Erdős's, as recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000406-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
