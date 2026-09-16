# JSP-000407: Erdős #508 (Hadwiger–Nelson), the classical lower bound χ(ℝ²) ≥ 4

This package submits, for intake and eligibility review, a Lean proof of the classical lower bound in [JSP-000407](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000407) / [Erdős Problem #508](https://www.erdosproblems.com/508), the Hadwiger–Nelson problem: what is the chromatic number `χ(ℝ²)` of the plane, the least number of colours such that no two points at distance `1` share a colour?

**Scope statement.** The problem is open; the best known bounds are `5 ≤ χ(ℝ²) ≤ 7` (de Grey 2018 for the lower bound). This package proves only the classical, now superseded, bound `χ(ℝ²) ≥ 4` by the Moser spindle (Moser–Moser 1961), which the problem page lists among the "several small graphs that show χ ≥ 4". De Grey's bound `≥ 5`, the upper bound `7`, and the value of `χ(ℝ²)` are not claimed.

## Statement and proof

[Erdos508MoserSpindle/Main.lean](Erdos508MoserSpindle/Main.lean) copies the formal-conjectures graph `UnitDistancePlaneGraph` verbatim (vertices a set `V ⊆ ℝ²`, adjacency `dist x y = 1`) and proves

```lean
theorem hadwiger_nelson_at_least_four :
    4 ≤ (UnitDistancePlaneGraph Set.univ).chromaticNumber
```

which is exactly the [formal-conjectures statement `Erdos508.HadwigerNelsonAtLeast4 : 4 ≤ χ(ℝ²)`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/508.lean) (`χ(ℝ²)` is their notation for `SimpleGraph.chromaticNumber (UnitDistancePlaneGraph Set.univ)`; the statement is tagged "research solved" there with a `sorry`).

Proof. The seven points `A = (0,0)`, `B = (1,0)`, `C = (1/2, √3/2)`, `D = (3/2, √3/2)` and `B', C', D'`, their images under the rotation about `A` with `cos θ = 5/6`, `sin θ = √11/6`, form two unit rhombi sharing `A` with `|DD'| = 1`; the eleven unit distances are verified from the Euclidean distance formula (`moser_dist_eq_one`). The kernel checks by `decide` that no map from the seven vertices to three colours is proper on these eleven edges (`moser_no_three_colouring`). If `χ(ℝ²) ≤ 3`, Mathlib's `chromaticNumber_le_iff_colorable` yields a proper `3`-colouring of the whole plane, whose restriction to the spindle contradicts this.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the graph definition by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound` (no `native_decide`; one `set_option maxRecDepth 10000` is a resource setting for the kernel `decide`). [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The construction is the Moser spindle (L. Moser and W. Moser, 1961). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000407-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
