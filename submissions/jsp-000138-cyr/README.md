# JSP-000138: Erdős #132, the n = 4 counterexample (two glued equilateral triangles)

This package submits, for intake and eligibility review, a Lean proof of the small counterexample recorded on the page of [JSP-000138](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000138) / [Erdős Problem #132](https://www.erdosproblems.com/132): for a set of `n` points in the plane, must there be two distances which occur at least once but between at most `n` pairs, and must the number of such distances tend to infinity?

**Scope statement.** The questions are open and are not addressed; the Erdős–Fishburn results for `n = 5, 6` and the Clemen–Dumitrescu–Liu bound are not claimed. The problem page records: "Erdős believed that for `n ≥ 5` there must always exist at least two such distances. This is false for `n = 4`, as witnessed by two equilateral triangles of the same side-length glued together." This package proves exactly that `n = 4` statement, with the formal-conjectures definitions `distanceSet` and `distanceMultiplicity` (`FormalConjecturesForMathlib/Geometry/Metric.lean`) copied verbatim; formal-conjectures has no file for #132, so the theorem statement is ours.

## Statement and proof

[Erdos132FourPoints/Main.lean](Erdos132FourPoints/Main.lean) proves

```lean
theorem erdos_132_four_points :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), #A = 4 ∧
      #{d ∈ distanceSet A | distanceMultiplicity A d ≤ 4} < 2
```

Proof. The witness is the rhombus `(0,0), (1,0), (1/2, √3/2), (1/2, −√3/2)`: five pairs are at distance `1` and one pair at distance `√3`, so the only distance of multiplicity at most `4` is `√3`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definitions by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The counterexample is the one recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000138-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
